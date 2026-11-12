-- Prove2me | Definitions.Def_SmallSecretLWE_Classical_Kikuchi
-- name    : SmallSecretLWE_Classical_Kikuchi
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:27:10.52819+00:00
-- url     : https://prove2.me/theorems/c1090b0c-15d1-48e7-a6c0-886a2e9ea412
-- title:
--   The Kikuchi multigraph $K_l(A)$, $\theta^{(n,l,k)}$, Construction 4.1, the hash $H$, $R$-faraway sets and Algorithm 1
-- statement:
--   Let $A\in\mathbb Z_q^{m\times n}$ with rows $a_1,\dots,a_m$. The **Kikuchi graph** $K_l(A)$ has vertex set $(\mathbb Z_q^n)_l$ and, for every row $a_i$ and all $u,v\in(\mathbb Z_q^n)_l$ with $v-u=a_i$, an edge $u\to v$ (sign $+$) and an edge $v\to u$ (sign $-$), both of **color** $i$. Edges are occurrences $(i,\sigma,u)$ with head $u+\sigma a_i$, so equal rows give parallel edges. The reverse of $(i,\sigma,u)$ is $(i,-\sigma,u+\sigma a_i)$.
--
--   The number of edges per row is given by Eq. (7):
--   $$\theta^{(n,l,k)}=2\sum_{r=0}^{k}\binom{k}{r}(q-2)^r\binom{k-r}{(k-r)/2}\binom{n-k}{l-(k+r)/2}(q-1)^{l-(k+r)/2},$$
--   with $\binom{t}{s}=0$ unless $s$ is an integer in $[0,t]$.
--
--   **Construction 4.1.** For a walk $W$ with edges $e_1,\dots,e_T$, $c\in\mathbb Z_q^m$ starts at $0$ and each step along an edge of color $i$ adds $+1$ (sign $+$) or $-1$ (sign $-$) to $c_i$.
--
--   **Hash (Eq. (10)).** For $0\le R<q/2$ let $h=\min\{q-1,\lfloor R/l\rfloor+1\}$; for $x\in(\mathbb Z_q^n)_l$ with support $j_1<\dots<j_l$ and entries read in $\{1,\dots,q-1\}$, $H(x)=\big((j_a)_a,(\lfloor (x_{j_a}-1)/h\rfloor)_a\big)$.
--
--   A set $S\subseteq(\mathbb Z_q^n)_l$ is **$R$-faraway** if $\|u-v\|_1>R$ for all distinct $u,v\in S$; it is a maximal $R$-faraway subset of $U$ if moreover $S\subseteq U$ and every $v\in U\setminus S$ has some $u\in S$ with $\|u-v\|_1\le R$.
--
--   **Algorithm 1 (Find-Good-Close-Walk$(A,l,T,R,\delta)$).** Set $N=\binom nl(q-1)^l$, $M=N/\binom{\lfloor R/4\rfloor+l}{l}$, $L=\lceil128\sqrt M\rceil$, $J=\lceil16\ln(1/\delta)\rceil$. For $b=1,\dots,J$: draw $w_0\sim\nu(K_l(A))$, then $L$ independent walks $W_1,\dots,W_L\sim\mathrm{walk}^T_{w_0}$; if some $i<j$ has $W_i,W_j$ good and $H$ of their terminal vertices equal, take the lexicographically first such pair and return $W_i^{\mathrm{rev}}\circ W_j$. After $J$ failures return FAIL.
--
--   **Formalization Note.** `KVert n q l`, `KEdge A l` (subtypes), `kikuchi A l : MultiDigraph`, `kColor`, `kRev`, `joinWalk p₁ p₂` $=W_1^{\mathrm{rev}}\circ W_2$, `theta`, `constrC`, `hashKey`, `IsFaraway`, `IsMaxFarawayIn`. Algorithm 1 is given by its output law: `alg1IterProb` is the probability that one iteration ends with a given outcome (`none`, or `some (w₀, W_i, W_j)`), and, iterations being independent, `alg1ReturnProb Q` $=\sum_{b<J}\Pr[\text{iteration fails}]^b\Pr[\text{iteration returns an outcome in }Q]$.
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), pp. 13–14, Constructions 3.13–3.14 and Eq. (7); p. 14, Construction 4.1; p. 18, Eq. (10) and Algorithm 1; p. 19, R-faraway sets

import Mathlib
import Definitions.Def_SmallSecretLWE_Classical_Basic
import Definitions.Def_SmallSecretLWE_Classical_Digraph

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace SmallSecretLWE.Classical

/-!
# The Kikuchi multigraph `K_l(A)`, `θ^{(n,l,k)}`, Construction 4.1, the hash `H` and Algorithm 1

Agrawal, Bagchi, Kumar, *Algorithms for Sparse LWE and LPN with Small Secrets*, STOC 2027
submission (manuscript sha256 8d93a268…): Constructions 3.13, 3.14 and Eq. (7), pp. 13–14;
Construction 4.1, p. 14; Eq. (10) and Algorithm 1, p. 18; R-faraway sets, p. 19.

* Vertices `KVert n q l = (Z_q^n)_l`, the vectors with exactly `l` nonzero entries.
* Construction 3.13: for every row `a = A_i` and all `u, v ∈ (Z_q^n)_l` with `v − u = a` there
  are edges `u –a→ v` and `v –(−a)→ u`, colored `i`. They are modelled as edge occurrences
  `(i, σ, u)` (row, sign `σ ∈ {+, −}` encoded as `true`/`false`, tail `u`) whose head
  `u + σ·a_i` lies in `(Z_q^n)_l`: the Kikuchi graph is a multigraph, so equal rows (or `q = 2`,
  where `a = −a`) give parallel edges, one per row and sign, as the count `θ` of Eq. (7) does.
* `theta n l k q` is the printed right-hand side of Eq. (7), in `ℝ`, with the convention of
  footnote 7 (`binom(t, s) = 0` unless `s` is an integer in `[0, t]`), and `x^0 = 1`.
* `kColor e = i` is the color (row index) of an edge (Observation 4.11).
* Construction 4.1: `constrC p` adds `+1` to `c_i` for every step along a `+`-edge of row `i`
  and `−1` for every `−`-edge, computed in `Z_q`; the row and sign are read from the recorded
  edge label.
* `kRev e` is the reverse edge `(i, −σ, u + σ a_i)`. `joinWalk p₁ p₂ = W₁^rev ∘ W₂`: the reversed
  edges of `p₁` in reverse order, then `p₂`; started at the terminal vertex of `p₁`.
* Eq. (10): `h = min{q − 1, ⌊R/l⌋ + 1}` and `H(x)` is the list of pairs
  `(j_a, ⌊(x_{j_a} − 1)/h⌋)` over the support `j_1 < … < j_l`, entries read in `{1, …, q−1}`.
* `R`-faraway: `‖u − v‖_1 > R` for all distinct `u, v ∈ S`; a maximal `R`-faraway subset of `U`
  is an `R`-faraway `S ⊆ U` such that every `v ∈ U \ S` has some `u ∈ S` with `‖u − v‖_1 ≤ R`.
* Algorithm 1 (Find-Good-Close-Walk): `N = binom(n,l)(q−1)^l`, `M = N / binom(⌊R/4⌋+l, l)`,
  `L = ⌈128 √M⌉`, `J = ⌈16 ln(1/δ)⌉`. One iteration draws `w₀ ∼ ν` and `L` independent walks
  `walk^T_{w₀}`; it succeeds with the lexicographically first pair `i < j` of good walks whose
  terminal vertices have equal keys `H`, and returns `(w₀, W_i, W_j)` (the returned walk is
  `joinWalk W_i W_j`). Iterations are independent, so the probability that the algorithm returns
  an output in `Q` is `Σ_{b < J} Pr[iteration fails]^b · Pr[iteration succeeds with output in Q]`
  (`alg1ReturnProb`); FAIL takes the remaining mass.
-/

/-- The vertices `(Z_q^n)_l` of the Kikuchi graph. -/
abbrev KVert (n q l : ℕ) := {x : Fin n → ZMod q // l0 x = l}

/-- The sign `σ ∈ {+1, −1}` of an edge (`true` is `+`). -/
def sgn {q : ℕ} (b : Bool) : ZMod q := if b then 1 else -1

/-- Edge occurrences `(i, σ, u)` of `K_l(A)`: row `i`, sign `σ`, tail `u`, with head
`u + σ a_i ∈ (Z_q^n)_l`. -/
abbrev KEdge {m n q : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod q)) (l : ℕ) :=
  {e : Fin m × Bool × KVert n q l // l0 (e.2.2.val + (sgn e.2.1 : ZMod q) • A e.1) = l}

/-- The head `u + σ a_i` of an edge occurrence. -/
def kHead {m n q : ℕ} {A : Matrix (Fin m) (Fin n) (ZMod q)} {l : ℕ} (e : KEdge A l) :
    KVert n q l :=
  ⟨e.1.2.2.val + (sgn e.1.2.1 : ZMod q) • A e.1.1, e.2⟩

/-- The Kikuchi multigraph `K_l(A)` (Construction 3.13). -/
def kikuchi {m n q : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod q)) (l : ℕ) :
    MultiDigraph (KVert n q l) (KEdge A l) :=
  ⟨fun e => e.1.2.2, kHead⟩

/-- The color of an edge: its row index (Observation 4.11). -/
def kColor {m n q : ℕ} {A : Matrix (Fin m) (Fin n) (ZMod q)} {l : ℕ} (e : KEdge A l) : Fin m :=
  e.1.1

/-- The reverse edge `(i, −σ, u + σ a_i)` from the head back to the tail. -/
def kRev {m n q : ℕ} {A : Matrix (Fin m) (Fin n) (ZMod q)} {l : ℕ} (e : KEdge A l) :
    KEdge A l :=
  ⟨(e.1.1, !e.1.2.1, kHead e), by
    have h : (kHead e).val + (sgn (!e.1.2.1) : ZMod q) • A e.1.1 = e.1.2.2.val := by
      simp only [kHead]
      cases e.1.2.1 <;> simp [sgn]
    simpa [h] using e.1.2.2.2⟩

/-- `θ^{(n,l,k)}`, the right-hand side of Eq. (7). -/
def theta (n l k q : ℕ) : ℝ :=
  2 * ∑ r ∈ Finset.range (k + 1),
    if Even (k - r) ∧ (k + r) / 2 ≤ l then
      (k.choose r : ℝ) * ((q : ℝ) - 2) ^ r * ((k - r).choose ((k - r) / 2) : ℝ) *
        ((n - k).choose (l - (k + r) / 2) : ℝ) * ((q : ℝ) - 1) ^ (l - (k + r) / 2)
    else 0

/-- Construction 4.1: `c_i = #{steps along a +-edge of row i} − #{steps along a −-edge of row i}`
in `Z_q`. -/
def constrC {m n q : ℕ} {A : Matrix (Fin m) (Fin n) (ZMod q)} {l T : ℕ} (p : Fin T → KEdge A l) :
    Fin m → ZMod q :=
  fun i => ∑ r, if (p r).1.1 = i then sgn (p r).1.2.1 else 0

/-- `W₁^rev ∘ W₂`: the reversed edges of `p₁` in reverse order, followed by `p₂`. -/
def joinWalk {m n q : ℕ} {A : Matrix (Fin m) (Fin n) (ZMod q)} {l T : ℕ}
    (p₁ p₂ : Fin T → KEdge A l) : Fin (T + T) → KEdge A l :=
  Fin.append (fun i => kRev (p₁ (Fin.rev i))) p₂

/-- The bucket width `h = min{q − 1, ⌊R/l⌋ + 1}` of Eq. (10). -/
def hashWidth (q l : ℕ) (R : ℝ) : ℕ := min (q - 1) (⌊R / l⌋₊ + 1)

/-- The hash key `H(x)` of Eq. (10): the pairs `(j_a, ⌊(x_{j_a} − 1)/h⌋)` over the support
`j_1 < … < j_l` of `x`, with `x_{j_a}` read in `{1, …, q − 1}`. -/
def hashKey {n q : ℕ} (l : ℕ) (R : ℝ) (x : Fin n → ZMod q) : List (ℕ × ℕ) :=
  ((List.finRange n).filter fun j => decide (x j ≠ 0)).map fun j =>
    (j.val, ((x j).val - 1) / hashWidth q l R)

/-- `S` is `R`-faraway: `‖u − v‖_1 > R` for all distinct `u, v ∈ S`. -/
def IsFaraway {n q l : ℕ} (R : ℝ) (S : Finset (KVert n q l)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → R < l1 (u.val - v.val)

/-- `S` is a maximal `R`-faraway subset of `U`. -/
def IsMaxFarawayIn {n q l : ℕ} (R : ℝ) (S U : Finset (KVert n q l)) : Prop :=
  S ⊆ U ∧ IsFaraway R S ∧ ∀ v ∈ U, v ∉ S → ∃ u ∈ S, l1 (u.val - v.val) ≤ R

/-- `N = binom(n, l)(q − 1)^l` (Algorithm 1, line 1). -/
def alg1N (n l q : ℕ) : ℝ := (n.choose l : ℝ) * ((q : ℝ) - 1) ^ l

/-- `M = N / binom(⌊R/4⌋ + l, l)` (Algorithm 1, line 1). -/
def alg1M (n l q : ℕ) (R : ℝ) : ℝ := alg1N n l q / ((⌊R / 4⌋₊ + l).choose l : ℝ)

/-- `L = ⌈128 √M⌉` (Algorithm 1, line 2). -/
def alg1L (n l q : ℕ) (R : ℝ) : ℕ := ⌈128 * Real.sqrt (alg1M n l q R)⌉₊

/-- `J = ⌈16 ln(1/δ)⌉` (Algorithm 1, line 2). -/
def alg1J (δ : ℝ) : ℕ := ⌈16 * Real.log (1 / δ)⌉₊

section Alg1

variable {m n q : ℕ} [NeZero q]

/-- The lexicographically first pair `i < j` of good walks whose terminal vertices have equal
hash keys (Algorithm 1, lines 7–8). -/
def alg1Pick (A : Matrix (Fin m) (Fin n) (ZMod q)) (l : ℕ) (R : ℝ) {T L : ℕ}
    (w₀ : KVert n q l) (ps : Fin L → Fin T → KEdge A l) : Option (Fin L × Fin L) :=
  ((List.finRange L) ×ˢ (List.finRange L)).find? fun ij =>
    decide (ij.1 < ij.2 ∧ (kikuchi A l).IsGood w₀ (ps ij.1) ∧ (kikuchi A l).IsGood w₀ (ps ij.2) ∧
      hashKey l R ((kikuchi A l).walkVtx w₀ (ps ij.1) (Fin.last T)).val =
        hashKey l R ((kikuchi A l).walkVtx w₀ (ps ij.2) (Fin.last T)).val)

/-- The probability that one iteration of Algorithm 1 (with `L` walks of length `T`) ends with
outcome in `Q` (`none`: no pair found; `some (w₀, W_i, W_j)`: return `W_i^rev ∘ W_j`). -/
def alg1IterProb (A : Matrix (Fin m) (Fin n) (ZMod q)) (l : ℕ) (R : ℝ) (T L : ℕ)
    (Q : Option (KVert n q l × (Fin T → KEdge A l) × (Fin T → KEdge A l)) → Prop) : ℝ :=
  ∑ w₀ : KVert n q l, (kikuchi A l).nu w₀ *
    ∑ ps : Fin L → Fin T → KEdge A l,
      if Q ((alg1Pick A l R w₀ ps).map fun ij => (w₀, ps ij.1, ps ij.2)) then
        ∏ i, (kikuchi A l).walkProb w₀ (ps i)
      else 0

/-- The probability that Algorithm 1, Find-Good-Close-Walk`(A, l, T, R, δ)`, returns
`W_i^rev ∘ W_j` for an iteration outcome `(w₀, W_i, W_j)` satisfying `Q`. -/
def alg1ReturnProb (A : Matrix (Fin m) (Fin n) (ZMod q)) (l T : ℕ) (R δ : ℝ)
    (Q : KVert n q l × (Fin T → KEdge A l) × (Fin T → KEdge A l) → Prop) : ℝ :=
  ∑ b ∈ Finset.range (alg1J δ),
    alg1IterProb A l R T (alg1L n l q R) (fun o => o = none) ^ b *
      alg1IterProb A l R T (alg1L n l q R) (fun o => ∃ x, o = some x ∧ Q x)

end Alg1

end SmallSecretLWE.Classical


