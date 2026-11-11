-- Prove2me | Definitions.Def_SAInterp_Res2_CPLSDist
-- name    : SAInterp_Res2_CPLSDist
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:40:33.431047+00:00
-- url     : https://prove2.me/theorems/0671b4b6-2f67-48c7-b7d8-b0db53426622
-- title:
--   The distributions D_k on CPLS_n assignments, the signed measure µ = Σ ω_k D_k with E_µ, and Q_a (Definition 6.1, Definition 7.5)
-- statement:
--   Fix $n$ and $1\le k\le n$. A sample of **$D_k$** (§4.1, §6) is a tuple $(\pi,S,\gamma,e)$ of independent uniform components:
--   - $\pi=(\pi_i)_{i\in[n-1]}$, a permutation per layer, with $\pi_i$ sending the successor of $(i,j)$ to $(i+1,\pi_i(j))$; this partitions the grid into $n$ disjoint top-to-bottom paths $P_1,\dots,P_n$, with $P_i$ through $(1,i)$;
--   - $S$, with $\{1\}\subseteq S\subseteq[n]$ and $|S|=k$ (the colourless paths);
--   - $\gamma\in[n]^{[n]}$, a colour per path;
--   - $e$, the values of the selectors above the bottom row.
--
--   The assignment $x(\pi,S,\gamma,e)$ to $\mathrm{CPLS}_n$ is defined as follows. Every node above the bottom row is active and every bottom-row node is inactive. Successors follow $\pi$. For $i\notin S$, every $v\in P_i$ has $c_{v,\gamma_i}=1$, and every other colour is $0$. The bottom node of $P_i$ has selector $\gamma_i$, and every other selector is given by $e$. $E_{D_k}[f\mid\pi]$ averages over $(S,\gamma,e)$, and $E_{D_k}[f]$ also averages over $\pi$. An element of the indicator algebra is evaluated at $x(\pi,S,\gamma,e)$.
--
--   With $d=\lfloor n/100\rfloor$ (Definition 6.1),
--   $$E_\mu[p]=\sum_{k=1}^{d+2}\omega^{(d+2)}_k\,E_{D_k}[p],$$
--   a signed combination of expectations. $X_i=1$ iff $i\notin S$. The polynomial of Definition 7.5 is
--   $$Q_a(z)=\frac{(n-z)_a}{(n-1)_a},$$
--   where $(y)_a=\prod_{i<a}(y-i)$. Lemma 7.7 uses $P(z)=\sum_{T\subseteq B}(-1)^{|T|}Q_{a+|T|}(z)\prod_{j\in T}\delta_j$.
--
--   **Formalization Note.** Indices are 0-based: path $P_i$ is `i - 1`, and the distinguished path is `0`, so $S\ni0$. The averages are finite sums divided by the number of terms. `layerPerm π r` composes $\pi_0,\dots,\pi_{r-1}$, and `pathOf π r j` is the index of the path through node $(r,j)$. The paper's $d=n/100$ is read as $\lfloor n/100\rfloor$: the proofs only use $d\le n/100$, and $\mu$ needs an integer $d$.
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 28 (§4.1 sampling of (π, S)), pp. 32–33 (§6, D_k, Definition 6.1, Equations (3)–(4)), p. 34 (Definition 7.5, X_i), p. 35 (Lemma 7.7's P)

import Mathlib
import Definitions.Def_SAInterp_Res2_Indicator
import Definitions.Def_SAInterp_Res2_CPLS
import Definitions.Def_SAInterp_Res2_Interp

namespace SAInterp.Res2

open Classical Polynomial

/-!
# The distributions `D_k`, the signed measure `µ` and `E_µ` for `CPLS_n`

Acheampong, Davis, Robere, *Polynomial Interpolation for Sherali-Adams Lower Bounds*,
STOC 2027 submission (manuscript sha256 8de0a787…), §4.1 (p. 28), §6 (pp. 32–33,
Definition 6.1), §7.1 (p. 34, Definition 7.5).

Indices are 0-based (see `Def_SAInterp_Res2_CPLS`). A sample of `D_k` is a tuple `(π, S, γ, e)`:
* `π : Fin (n − 1) → Perm (Fin n)`, one uniformly random permutation per layer; `π_i` sends the
  successor of node `(i, j)` to `(i + 1, π_i j)`. The paths `P_0, …, P_{n−1}` are the orbits from
  the top row: `P_i` passes through `(0, i)` (the paper's `(1, i + 1)`).
* `S`, uniform among the sets `S ⊆ Fin n` with `0 ∈ S` and `|S| = k` (the colourless paths;
  `0` is the distinguished path through the source).
* `γ : Fin n → Fin n`, a uniform colour for every path.
* `e : Fin (n − 1) → Fin n → Fin n`, uniform values of the selectors above the bottom row.
All four components are independent; `D_k` is the uniform average over them.
-/

/-- The layer permutations `π = (π_i)_{i ∈ [n−1]}`. -/
abbrev LayerPerms (n : ℕ) := Fin (n - 1) → Equiv.Perm (Fin n)

/-- The internal selector values `e_{(i,j)}` for the rows `i` above the bottom row. -/
abbrev InternalSel (n : ℕ) := Fin (n - 1) → Fin n → Fin n

/-- `layerPerm π r = π_{r−1} ∘ ⋯ ∘ π_0`: the column on row `r` of the path that starts at column
`c` on row `0` is `layerPerm π r c`. -/
def layerPerm {n : ℕ} (π : LayerPerms n) : ℕ → Equiv.Perm (Fin n)
  | 0 => 1
  | r + 1 => (if h : r < n - 1 then π ⟨r, h⟩ else 1) * layerPerm π r

/-- The index `i` of the path `P_i` containing the node `(r, j)`. -/
def pathOf {n : ℕ} (π : LayerPerms n) (r j : Fin n) : Fin n := (layerPerm π r.val).symm j

/-- The assignment `x(π, S, γ, e)` to `CPLS_n` (§6, p. 32–33): rows above the bottom row are
active and the bottom row inactive; successors follow `π`; the node `v ∈ P_i` has
`c_{v,γ_i} = 1` iff `i ∉ S`, and all other colours are `0`; the bottom-row selector of `P_i`
is `γ_i`; the other selectors are given by `e`. -/
def sampleAssign (n : ℕ) (π : LayerPerms n) (S : Finset (Fin n)) (γ : Fin n → Fin n)
    (e : InternalSel n) : MVAssignment (cplsSize n) := fun v =>
  match v with
  | .act i _ => (if i.val + 1 < n then 1 else 0 : Fin 2)
  | .succ i j => π i j
  | .col i j α => (if pathOf π i j ∉ S ∧ γ (pathOf π i j) = α then 1 else 0 : Fin 2)
  | .sel i j => if h : i.val + 1 < n then e ⟨i.val, by omega⟩ j else γ (pathOf π i j)

/-- The admissible colourless-path sets: `{1} ⊆ S ⊆ [n]` with `|S| = k` (0-based: `0 ∈ S`). -/
noncomputable def colourlessSets (n k : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter fun S => (∃ i ∈ S, i.val = 0) ∧ S.card = k

/-- `E_{D_k}[f | π]`: the average of `f(S, γ, e)` over `S ∈ colourlessSets n k` and all `γ`, `e`
(uniform and independent), for the fixed layer permutations `π`. -/
noncomputable def EDkCond (n k : ℕ) (f : Finset (Fin n) → (Fin n → Fin n) → InternalSel n → ℝ) :
    ℝ :=
  (∑ S ∈ colourlessSets n k, ∑ γ : Fin n → Fin n, ∑ e : InternalSel n, f S γ e) /
    (((colourlessSets n k).card : ℝ) * (Fintype.card (Fin n → Fin n) : ℝ) *
      (Fintype.card (InternalSel n) : ℝ))

/-- `E_{D_k}[f]`: the average of `E_{D_k}[f | π]` over uniformly random layer permutations. -/
noncomputable def EDk (n k : ℕ)
    (f : LayerPerms n → Finset (Fin n) → (Fin n → Fin n) → InternalSel n → ℝ) : ℝ :=
  (∑ π : LayerPerms n, EDkCond n k (f π)) / (Fintype.card (LayerPerms n) : ℝ)

/-- `E_{D_k}[p | π]` for an element `p` of the indicator algebra `A(X)` of `CPLS_n`. -/
noncomputable def EDkAlgCond (n k : ℕ) (π : LayerPerms n) (p : IndAlg (cplsSize n)) : ℝ :=
  EDkCond n k fun S γ e => evalAlg (sampleAssign n π S γ e) p

/-- `E_{D_k}[p]` for `p ∈ A(X)`. -/
noncomputable def EDkAlg (n k : ℕ) (p : IndAlg (cplsSize n)) : ℝ :=
  EDk n k fun π S γ e => evalAlg (sampleAssign n π S γ e) p

/-- `d = n/100` (Definition 6.1), read as `⌊n/100⌋`. -/
def cplsD (n : ℕ) : ℕ := n / 100

/-- `E_µ[p] = ∑_{k=1}^{d+2} ω_k^{(d+2)} E_{D_k}[p]` for `µ = ∑_{k=1}^{d+2} ω_k^{(d+2)} D_k`
(Definition 6.1, Equations (3), (4)), `d = ⌊n/100⌋`; a signed combination of expectations. -/
noncomputable def Emu (n : ℕ) (p : IndAlg (cplsSize n)) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (cplsD n + 2), omega (cplsD n + 2) k * EDkAlg n k p

/-- `Q_a(z) = (n − z)_a / (n − 1)_a` (Definition 7.5), with the falling factorial
`(y)_a = ∏_{i < a} (y − i)`. -/
noncomputable def Qpoly (n a : ℕ) : ℝ[X] :=
  C (1 / ∏ i ∈ Finset.range a, ((n : ℝ) - 1 - i)) * ∏ i ∈ Finset.range a, (C ((n : ℝ) - i) - X)

/-- `X_i(S) = 1` if `i ∉ S` (path `P_i` is coloured), else `0`. -/
noncomputable def Xind {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ℝ := if i ∈ S then 0 else 1

/-- The polynomial of Lemma 7.7: `P(z) = ∑_{T ⊆ B} (−1)^{|T|} Q_{a+|T|}(z) ∏_{j ∈ T} δ_j`. -/
noncomputable def lemma77Poly (n a : ℕ) (B : Finset (Fin n)) (δ : Fin n → ℝ) : ℝ[X] :=
  ∑ T ∈ B.powerset, C ((-1 : ℝ) ^ T.card * ∏ j ∈ T, δ j) * Qpoly n (a + T.card)

end SAInterp.Res2


