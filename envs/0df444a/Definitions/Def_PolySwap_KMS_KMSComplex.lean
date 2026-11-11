-- Prove2me | Definitions.Def_PolySwap_KMS_KMSComplex
-- name    : PolySwap_KMS_KMSComplex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:40:42.272826+00:00
-- url     : https://prove2.me/theorems/0da3de00-98e7-4884-a097-cea854747e69
-- title:
--   Congruence KMS complexes $X(A_d,\mathbb F_q,f)$, nice collections of colour sets, vertex links $Y$ and bin factors $Y_\ell$
-- statement:
--   Fix $d\ge2$ and a finite field $\mathbb F_q$. In $SL_{d+1}(\mathbb F_q[t])$ let $e_{i,j}(f)$ be the elementary matrix with $f$ at position $(i,j)$, and set
--   $$U_i=\langle e_{i,i+1}(\lambda)\mid\lambda\in\mathbb F_q\rangle\ (1\le i\le d),\quad U_0=\langle e_{d+1,1}(\lambda t)\mid\lambda\in\mathbb F_q\rangle,\quad U_J=\langle U_i\mid i\in J\rangle,\quad H_i=U_{[d]\setminus\{i\}}.$$
--   For an irreducible $f$ of degree $\ge2$, $\pi_f:SL_{d+1}(\mathbb F_q[t])\to SL_{d+1}(\mathbb F_q[t]/(f))$ and $H^f_i=\pi_f(H_i)$; the **congruence KMS complex** is
--   $$X(A_d,\mathbb F_q,f)=CC\big(SL_{d+1}(\mathbb F_q[t]/(f));(H^f_i)_{i\in[d]}\big)$$
--   with the uniform distribution, the vertex $gH^f_i$ having colour $i$. $F^{\mathcal I}X$ is its colored faces complex.
--
--   **Nice collections (Definition 3.6).** For $J\subseteq[d]$ with $|J|=r+1$, choose $j_0\in J$ and relabel all colours cyclically so that $j_0\mapsto0$ and the following colours become $1,\dots,d$; write $J=\{0=j_0<\dots<j_r\}$, $j_{r+1}=d+1$; the **$J$-bins** are $B_\ell=\{j_\ell+1,\dots,j_{\ell+1}-1\}=[a,b]$, $0\le\ell\le r$. $\mathcal I\in\binom{[d]}{r+1}^{[T]}$ is **nice** if for every $J\in\mathcal I$ (in $J$'s relabelling) every nonempty bin $B=[a,b]$ satisfies: (a) $|b-a|>100$; (b) some $I'\in\mathcal I\setminus\{J\}$ has $I'\cap B\subseteq[a,a+\lfloor\frac{b-a}5\rfloor]$; (c) some $I'$ has $I'\cap B\subseteq[b-\lfloor\frac{b-a}5\rfloor,b]$; (d) some $I'$ has $I'\cap B\subseteq[a+2\lceil\frac{b-a}5\rceil,a+3\lfloor\frac{b-a}5\rfloor]$; and (e) for every pair of $J$-bins $B=[a,b]$, $B'=[a',b']$ ($B=B'$ allowed) and $\ell,\ell'\in\{0,1,2,3\}$ some $I'\in\mathcal I\setminus\{J\}$ misses both $[a+\ell\lfloor\frac{b-a}5\rfloor,\min\{a+(\ell+2)\lceil\frac{b-a}5\rceil+4,b\}]$ and the analogous interval of $B'$.
--
--   **Links and bins (§3.3, §6, §7).** For fixed $J\in\mathcal I$, in $J$'s path order, $U_B=\langle e_{i,i+1}(\lambda):i\in B,\lambda\in\mathbb F_q\rangle\le SL_{d+1}(\mathbb F_q)$ and $H^B_I=U_{B\setminus I}$. The vertex link of $F^{\mathcal I}X$ at a vertex of colour $J$ is
--   $$Y=CC\big(U_{[d]\setminus J};(H^{[d]\setminus J}_I)_{I\in\mathcal I\setminus\{J\}}\big),\qquad Y_\ell=CC\big(U_{B_\ell};(H^{B_\ell}_I)_{I\in\mathcal I\setminus\{J\}}\big)$$
--   are its bin factors; $\mathrm{Dehn}_Y=\mathrm{Dehn}_{S,R}$ and $\mathrm{Dehn}_{Y_\ell}=\mathrm{Dehn}_{S_\ell,R_\ell}$ are the coset-complex Dehn functions. An upper-triangular $g$ is **supported on block size $k$** if $g=\mathrm{diag}(I_{k'},A,I_{k''})$ with $A$ of size $k\times k$.
--
--   **Formalization Note.** Matrix indices are `Fin (d+1)` (0-based: the paper's $e_{i,i+1}$ is `transvection (i-1) i`); colours are natural numbers $0,\dots,d$. `kmsX d F f` uses `AdjoinRoot f` for $\mathbb F_q[t]/(f)$. The relabelling base is $j_0=\min J$ (`base`); Definition 3.6 notes the conditions do not depend on this choice. Bins are indexed by $\ell<|J|$ through `binLo`/`binHi` ($a=j_\ell+1$, $b=j_{\ell+1}-1$; empty when $b<a$); in (e) the two bins range over all pairs $(\ell,\ell')$, $\ell=\ell'$ included (as the count in the proof of Lemma 3.7, p. 34, does). In `linkY`, `binY` the family is indexed by the subtype `{K // K ∈ I.erase J}` and each subgroup is taken inside the ambient group via `subgroupOf`. `niceCount d r T` counts the nice members of $\binom{[d]}{r+1}^{[T]}$.
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), §2.3 (p. 15), §3.1 (pp. 23–24, Definition 3.6), §3.3 (p. 27), §3.4 (p. 28), §6 (p. 47), §7 (p. 50)

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Dehn

open Classical Polynomial Matrix

noncomputable section

namespace PolySwap.KMS

/-!
# Congruence KMS complexes `X(A_d, F_q, f)`, nice colour collections, vertex links and bins

Dikstein, Oppenheim, Valentiner-Branth, *Polynomial Swap Coboundary Expansion with Applications
to LTCs and PCPs*, STOC 2027 submission (manuscript sha256 b9cb2095…), §2.3 (p. 15), §3.1
(pp. 23–24, Definition 3.6), §3.3 (p. 27), §3.4 (p. 28), §6 (p. 47), §7 (p. 50).

Matrices are indexed by `Fin (d + 1)`; the paper's 1-based row/column `i` is `i - 1`. Colours
are the natural numbers `0, …, d` (`[d] = {0, …, d}`, p. 9).
-/

section KMS

variable (d : ℕ) (F : Type*) [Field F]

/-- The generators of the root group `U_c` of colour `c ∈ [d]` in `SL_{d+1}(F_q[t])` (p. 15):
`e_{c,c+1}(λ)` (`λ ∈ F_q`) for `1 ≤ c ≤ d`, and `e_{d+1,1}(λt)` for `c = 0`; here `e_{i,j}(f)`
is the elementary matrix (transvection) with `f` at position `(i, j)` (1-based). -/
def rootGens (c : ℕ) : Set (SpecialLinearGroup (Fin (d + 1)) F[X]) :=
  {g | ∃ (lam : F) (i j : Fin (d + 1)),
    ((1 ≤ c ∧ c ≤ d ∧ (i : ℕ) = c - 1 ∧ (j : ℕ) = c ∧
        (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F[X]) = transvection i j (C lam)) ∨
      (c = 0 ∧ (i : ℕ) = d ∧ (j : ℕ) = 0 ∧
        (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F[X]) = transvection i j (C lam * X)))}

/-- `U_J = ⟨U_c | c ∈ J⟩ ≤ SL_{d+1}(F_q[t])` (p. 15). -/
def U (J : Finset ℕ) : Subgroup (SpecialLinearGroup (Fin (d + 1)) F[X]) :=
  Subgroup.closure (⋃ c ∈ J, rootGens d F c)

/-- `H_c = U_{[d] \ {c}}` (p. 15). -/
def Hcol (c : ℕ) : Subgroup (SpecialLinearGroup (Fin (d + 1)) F[X]) :=
  U d F ((Finset.range (d + 1)).erase c)

/-- `H^f_c = π_f(H_c) ≤ SL_{d+1}(F_q[t]/(f))`, with `π_f` induced by `F_q[t] → F_q[t]/(f)`
(p. 15). -/
def Hf (f : F[X]) (c : ℕ) : Subgroup (SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) :=
  (Hcol d F c).map (SpecialLinearGroup.map (AdjoinRoot.mk f))

/-- The congruence KMS complex `X(A_d, F_q, f) = CC(SL_{d+1}(F_q[t]/(f)); (H^f_i)_{i ∈ [d]})`
(p. 15), with the uniform top-level distribution. The colour of the vertex `⟨i, gH^f_i⟩` is
`i`. -/
def kmsX (f : F[X]) :
    WComplex (Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i) :=
  cosetComplex (SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) (fun i : Fin (d + 1) => Hf d F f (i : ℕ))

/-- The colour `col(v) ∈ [d]` of a vertex of `X(A_d, F_q, f)`. -/
def kmsCol (f : F[X]) :
    (Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i) → ℕ :=
  fun v => (v.1 : ℕ)

/-- The colored faces complex `F^I X(A_d, F_q, f)` (Definition 2.14). -/
def kmsFI (f : F[X]) (I : Finset (Finset ℕ)) :
    WComplex (Finset (Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i)) :=
  (kmsX d F f).coloredFaces (kmsCol d F f) I

end KMS

section Nice

/-- The cyclic relabelling of colours that sends `j₀` to `0` and the colours following it to
`1, …, d` (Definition 3.6). -/
def relabel (d j₀ c : ℕ) : ℕ := (c + (d + 1) - j₀) % (d + 1)

/-- The base colour `j₀ ∈ J` used for the relabelling of `J` (the least element of `J`; the
paper notes that the choice does not matter). -/
def base (J : Finset ℕ) : ℕ := if h : J.Nonempty then J.min' h else 0

/-- A colour set `K` in the path order chosen for `J`. -/
def rl (d : ℕ) (J K : Finset ℕ) : Finset ℕ := K.image (relabel d (base J))

/-- `j_k` for the relabelled `J = {0 = j₀ < j₁ < ⋯ < j_r}`, and `j_{r+1} = d + 1`. -/
def jAt (d : ℕ) (J : Finset ℕ) (k : ℕ) : ℕ :=
  if k < J.card then ((rl d J J).sort (· ≤ ·)).getD k 0 else d + 1

/-- The left end `a = j_ℓ + 1` of the `ℓ`-th `J`-bin. -/
def binLo (d : ℕ) (J : Finset ℕ) (ℓ : ℕ) : ℕ := jAt d J ℓ + 1

/-- The right end `b = j_{ℓ+1} - 1` of the `ℓ`-th `J`-bin. -/
def binHi (d : ℕ) (J : Finset ℕ) (ℓ : ℕ) : ℕ := jAt d J (ℓ + 1) - 1

/-- The `ℓ`-th `J`-bin `B_ℓ = {j_ℓ + 1, …, j_{ℓ+1} - 1} = [a, b]` (Definition 3.6), in the path
order of `J`; it is empty when `b < a`. -/
def bin (d : ℕ) (J : Finset ℕ) (ℓ : ℕ) : Finset ℕ := Finset.Icc (binLo d J ℓ) (binHi d J ℓ)

/-- The window `[a + s⌊(b-a)/5⌋, min{a + (s+2)⌈(b-a)/5⌉ + 4, b}]` of condition (e). -/
def window (a b s : ℕ) : Finset ℕ :=
  Finset.Icc (a + s * ((b - a) / 5)) (min (a + (s + 2) * ((b - a + 4) / 5) + 4) b)

/-- A collection `I` of disjoint colour sets is *nice* (Definition 3.6): for every `J ∈ I`, in
the path order chosen for `J`, every nonempty `J`-bin `B = [a, b]` satisfies
(a) `|b - a| > 100`;
(b) some `I' ∈ I \ {J}` has `I' ∩ B ⊆ [a, a + ⌊(b-a)/5⌋]`;
(c) some `I' ∈ I \ {J}` has `I' ∩ B ⊆ [b - ⌊(b-a)/5⌋, b]`;
(d) some `I' ∈ I \ {J}` has `I' ∩ B ⊆ [a + 2⌈(b-a)/5⌉, a + 3⌊(b-a)/5⌋]`;
and (e) for every pair of nonempty `J`-bins `B = [a, b]`, `B' = [a', b']` (`B = B'` allowed, as
in the count of §4, p. 34) and all
`s, s' ∈ {0, 1, 2, 3}` some `I' ∈ I \ {J}` misses both windows
`[a + s⌊(b-a)/5⌋, min{a + (s+2)⌈(b-a)/5⌉ + 4, b}]` and the analogous window of `B'`.
Empty bins are omitted. -/
def IsNice (d : ℕ) (I : Finset (Finset ℕ)) : Prop :=
  ∀ J ∈ I,
    (∀ ℓ < J.card, binLo d J ℓ ≤ binHi d J ℓ → 100 < binHi d J ℓ - binLo d J ℓ) ∧
    (∀ ℓ < J.card, binLo d J ℓ ≤ binHi d J ℓ → ∃ K ∈ I.erase J, ∀ c ∈ rl d J K,
        c ∈ bin d J ℓ → c ≤ binLo d J ℓ + (binHi d J ℓ - binLo d J ℓ) / 5) ∧
    (∀ ℓ < J.card, binLo d J ℓ ≤ binHi d J ℓ → ∃ K ∈ I.erase J, ∀ c ∈ rl d J K,
        c ∈ bin d J ℓ → binHi d J ℓ - (binHi d J ℓ - binLo d J ℓ) / 5 ≤ c) ∧
    (∀ ℓ < J.card, binLo d J ℓ ≤ binHi d J ℓ → ∃ K ∈ I.erase J, ∀ c ∈ rl d J K,
        c ∈ bin d J ℓ →
          binLo d J ℓ + 2 * ((binHi d J ℓ - binLo d J ℓ + 4) / 5) ≤ c ∧
            c ≤ binLo d J ℓ + 3 * ((binHi d J ℓ - binLo d J ℓ) / 5)) ∧
    (∀ ℓ < J.card, ∀ ℓ' < J.card, binLo d J ℓ ≤ binHi d J ℓ →
        binLo d J ℓ' ≤ binHi d J ℓ' → ∀ s ≤ 3, ∀ s' ≤ 3, ∃ K ∈ I.erase J,
          Disjoint (rl d J K) (window (binLo d J ℓ) (binHi d J ℓ) s) ∧
          Disjoint (rl d J K) (window (binLo d J ℓ') (binHi d J ℓ') s'))

/-- The number of nice collections in `([d] choose r+1)^[T]`. -/
def niceCount (d r T : ℕ) : ℕ := ((disjointColorSets d r T).filter (IsNice d)).card

end Nice

section Link

variable (d : ℕ) (F : Type*) [Field F]

/-- In the upper-triangular model of a vertex link (§3.3, p. 27; §6–§7): for a set `B` of
(relabelled) colours, `U_B = ⟨e_{i,i+1}(λ) | i ∈ B, 1 ≤ i ≤ d, λ ∈ F_q⟩ ≤ SL_{d+1}(F_q)`. -/
def UL (B : Finset ℕ) : Subgroup (SpecialLinearGroup (Fin (d + 1)) F) :=
  Subgroup.closure {g | ∃ (lam : F) (i j : Fin (d + 1)), (j : ℕ) ∈ B ∧ 1 ≤ (j : ℕ) ∧
    (i : ℕ) + 1 = j ∧ (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = transvection i j lam}

/-- The colours `[d] \ J` in the path order of `J` (so `0 ∈ J`). -/
def compl (J : Finset ℕ) : Finset ℕ := Finset.range (d + 1) \ rl d J J

/-- The subgroups `H^{[d]\J}_I = U_{([d]\J) \ I}` of `U_{[d]\J}`, `I ∈ I \ {J}` (§6, p. 47). -/
def linkH (I : Finset (Finset ℕ)) (J : Finset ℕ) (K : {K // K ∈ I.erase J}) :
    Subgroup (UL d F (compl d J)) :=
  (UL d F (compl d J \ rl d J K.1)).subgroupOf (UL d F (compl d J))

/-- The vertex link `Y = CC(U_{[d]\J}; (H^{[d]\J}_I)_{I ∈ I \ {J}})` of `F^I X` at a vertex of
colour `J` (§3.3, p. 27; §6, p. 47), in the path order of `J`. -/
def linkY (I : Finset (Finset ℕ)) (J : Finset ℕ) :
    WComplex (Σ K : {K // K ∈ I.erase J}, (UL d F (compl d J)) ⧸ linkH d F I J K) :=
  cosetComplex (UL d F (compl d J)) (linkH d F I J)

/-- `Dehn_Y` for the coset-complex presentation of `Y` (Definition 2.35, §6 p. 47). -/
def linkDehn (I : Finset (Finset ℕ)) (J : Finset ℕ) (t : ℕ) : ℕ∞ :=
  cosetDehn (linkH d F I J) t

/-- The subgroups `H^{B_ℓ}_I = U_{B_ℓ \ I}` of `U_{B_ℓ}` (§6, p. 47). -/
def binH (I : Finset (Finset ℕ)) (J : Finset ℕ) (ℓ : ℕ) (K : {K // K ∈ I.erase J}) :
    Subgroup (UL d F (bin d J ℓ)) :=
  (UL d F (bin d J ℓ \ rl d J K.1)).subgroupOf (UL d F (bin d J ℓ))

/-- The bin factor `Y_ℓ = CC(U_{B_ℓ}; (H^{B_ℓ}_I)_{I ∈ I \ {J}})` (§3.4, p. 28; §6, p. 47). -/
def binY (I : Finset (Finset ℕ)) (J : Finset ℕ) (ℓ : ℕ) :
    WComplex (Σ K : {K // K ∈ I.erase J}, (UL d F (bin d J ℓ)) ⧸ binH d F I J ℓ K) :=
  cosetComplex (UL d F (bin d J ℓ)) (binH d F I J ℓ)

/-- `Dehn_{Y_ℓ} = Dehn_{S_ℓ, R_ℓ}` (§6, p. 47; §7, p. 50). -/
def binDehn (I : Finset (Finset ℕ)) (J : Finset ℕ) (ℓ : ℕ) (s : ℕ) : ℕ∞ :=
  cosetDehn (binH d F I J ℓ) s

/-- An upper-triangular matrix `g` is supported on block size `k` (§6, p. 47):
`g = diag(I_{k'}, A, I_{k''})` with `A` a `k × k` block, i.e. `g` agrees with the identity outside
a diagonal block of `k` consecutive coordinates. -/
def SupportedOnBlock (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) (k : ℕ) : Prop :=
  ∃ lo : ℕ, ∀ i j : Fin (d + 1), ¬ (lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + k ∧ lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + k) →
    g i j = if i = j then 1 else 0

end Link

end PolySwap.KMS


