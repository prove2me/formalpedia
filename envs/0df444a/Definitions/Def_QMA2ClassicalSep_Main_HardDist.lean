-- Prove2me | Definitions.Def_QMA2ClassicalSep_Main_HardDist
-- name    : QMA2ClassicalSep_Main_HardDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:07.106342+00:00
-- url     : https://prove2.me/theorems/65ce8c94-3e55-482b-8fa1-4c894107be75
-- title:
--   §5 — hard YES/NO distributions, blocks, $\Theta_{\mathrm{size}}$, good parameters, $P_N$ and $h_{\mathrm{Sep}}$
-- statement:
--   Here $N=2^k$, $|\mathcal X_A|=|\mathcal X_B|=N^3$ ($\ell=3k$), $K=N^2$, $\mu=N$, $\varepsilon_0=1/40$. Sign functions $h_A,h_B$ give $\chi(x)=h_A(x_A)h_B(x_B)$.
--
--   **YES distribution $\mathcal D_+$.** Independent uniform permutations $\pi_p$ of $V$ and signs $\sigma_p(x)=\chi(x)\chi(\pi_p(x))$. Every parameter $((\pi_p),h_A,h_B)$ has positive probability, so $\operatorname{supp}\mathcal D_+$ is the set of all of them.
--
--   **NO distribution $\mathcal D_-$.** A labeling $\theta=(c_A,c_B)$ assigns each coordinate a pair of labels in $\mathcal C=[N]^2$; a vertex gets $c(x)=(c_A(x_A),c_B(x_B))\in[N]^4$. For a four-element set $Q\subseteq[N]$, $\mathcal B_Q$ is the set of vertices whose labels are an ordering of $Q$, and $\mathcal B_{\mathrm{remainder}}$ collects the vertices with a repeated label. Each $\pi_p$ is a uniform permutation of every nonempty block, and
--   $$
--   \sigma_p(x)=\chi(x)\chi(y)s_\theta(x,y),\qquad y=\pi_p(x),
--   $$
--   with $s_\theta(x,y)=\varepsilon(x)\varepsilon(y)$ on four-label blocks ($\varepsilon(x)$ the sign of the permutation sorting $c(x)$) and $s_\theta=-1$ on the remainder. $\operatorname{supp}\mathcal D_-$ consists of the parameters whose permutations preserve all blocks.
--
--   **Balanced labelings** (4): $\Theta_{\mathrm{size}}$ requires $(1-\varepsilon_0)\mu\le|C_I^P(\theta)|\le(1+\varepsilon_0)\mu$ for $P\in\{A,B\}$, $I\in\mathcal C$. $\bar\Gamma=\mathbb E[\Gamma\mid c_A,c_B,h_A,h_B]$ averages over the blockwise uniform permutations. A NO parameter is **good** if it lies in the support, $\theta\in\Theta_{\mathrm{size}}$, and $\|\Gamma-\bar\Gamma\|\le1/8$ (operator norm). `probLabeling` and `probNo` are the probabilities under $\nu$ (uniform labelings) and $\mathcal D_-$.
--
--   **Antisymmetric projector.** $|\mathrm{Alt}_Q\rangle=24^{-1/2}\sum_{\pi\in S_4}\operatorname{sgn}(\pi)|q_{\pi(1)},q_{\pi(2)}\rangle_A|q_{\pi(3)},q_{\pi(4)}\rangle_B$, $P_N=\sum_Q|\mathrm{Alt}_Q\rangle\langle\mathrm{Alt}_Q|$, and $h_{\mathrm{Sep}}(M)=\max_{\|\alpha\|=\|\beta\|=1}\langle\alpha\otimes\beta|M|\alpha\otimes\beta\rangle$.
--
--   **Formalization Note** Labels are 0-based (`Fin N`); label $i+1$ of the source is $i$. The NO permutations are drawn, given $\theta$, uniformly from the tuples preserving every block, which is the product of independent blockwise uniform permutations.
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, Section 5, pp. 19–23 (hard distributions, Equations (3)–(4), proof of Proposition 5.3) and start of Section 6, p. 24 (good NO parameters)

import Definitions.Def_QMA2ClassicalSep_Main_Instance

set_option autoImplicit false

/-!
# Section 5: the hard YES and NO distributions; the antisymmetric projector; good parameters

Grewal, Mutreja, Tomer, *A classical oracle separation between QMA and QMA(2)*, STOC 2027
submission #618, Section 5, pp. 19–23 (with the start of Section 6, p. 24). Throughout `N = 2^k`
(`k ≥ 2` is assumed by the theorems), `|𝒳_A| = |𝒳_B| = N³`, i.e. `ℓ = 3k`.
-/

namespace QMA2ClassicalSep.Main

open Matrix
open scoped Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- Labels `[N] = {1, …, N}`, written 0-based as `Fin N` (`N = 2^k`); label `i + 1` of the
source is `i : Fin N`. -/
abbrev Lbl (k : ℕ) := Fin (2 ^ k)

/-- `𝒞 = [N]²`: ordered pairs of labels, repeated labels allowed. -/
abbrev LPair (k : ℕ) := Lbl k × Lbl k

/-- The hard-instance vertex set `V = 𝒳_A × 𝒳_B`, `|𝒳_A| = |𝒳_B| = N³ = 2^{3k}`. -/
abbrev HVtx (k : ℕ) := Vtx (3 * k)

/-- A pair-label assignment `θ = (c_A, c_B)`, `c_P : 𝒳_P → 𝒞`. -/
abbrev Labeling (k : ℕ) := (Coord (3 * k) → LPair k) × (Coord (3 * k) → LPair k)

/-- A coordinate sign function `h_P : 𝒳_P → {±1}`. -/
abbrev SignFn (k : ℕ) := Coord (3 * k) → ℤˣ

/-- The four labels `c(x) = (c_A(x_A), c_B(x_B)) ∈ [N]⁴` of a vertex (as natural numbers). -/
def labels {k : ℕ} (θ : Labeling k) (x : HVtx k) : Fin 4 → ℕ :=
  ![(θ.1 x.1).1.val, (θ.1 x.1).2.val, (θ.2 x.2).1.val, (θ.2 x.2).2.val]

/-- The four labels of `x` are distinct (`x` lies in a four-label block). -/
def FourDistinct {k : ℕ} (θ : Labeling k) (x : HVtx k) : Prop :=
  Function.Injective (labels θ x)

/-- The set of labels of `x`. -/
def labelSet {k : ℕ} (θ : Labeling k) (x : HVtx k) : Finset ℕ :=
  Finset.univ.image (labels θ x)

/-- `x` and `y` lie in the same block: both in `ℬ_Q` for one four-element set `Q` (their
four labels are distinct and form the same set), or both in `ℬ_remainder`. -/
def SameBlock {k : ℕ} (θ : Labeling k) (x y : HVtx k) : Prop :=
  (FourDistinct θ x ∧ FourDistinct θ y ∧ labelSet θ x = labelSet θ y) ∨
    (¬ FourDistinct θ x ∧ ¬ FourDistinct θ y)

/-- The block `𝔅_θ(x)` containing `x`. -/
noncomputable def blockOf {k : ℕ} (θ : Labeling k) (x : HVtx k) : Finset (HVtx k) :=
  Finset.univ.filter (fun y => SameBlock θ x y)

/-- The number of inversions of a finite sequence. -/
noncomputable def inversions {n : ℕ} (f : Fin n → ℕ) : ℕ :=
  (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2 ∧ f ij.2 < f ij.1)).card

/-- The sign of the permutation that sorts a sequence of distinct numbers, `(−1)^{#inversions}`. -/
noncomputable def sortSign {n : ℕ} (f : Fin n → ℕ) : ℤ := (-1) ^ inversions f

/-- `ε(x)`: the sign of the permutation that sorts `c(x)` (footnote 5). -/
noncomputable def eps {k : ℕ} (θ : Labeling k) (x : HVtx k) : ℤ := sortSign (labels θ x)

/-- The sign label `s_θ(x, y)` for `x, y` in the same block: `ε(x)ε(y)` on a four-label block,
`−1` on the remainder block. -/
noncomputable def sθ {k : ℕ} (θ : Labeling k) (x y : HVtx k) : ℤ :=
  if FourDistinct θ x then eps θ x * eps θ y else -1

/-- `χ(x) = h_A(x_A) h_B(x_B)`. -/
def chi {k : ℕ} (hA hB : SignFn k) (x : HVtx k) : ℤ := (hA x.1 : ℤ) * (hB x.2 : ℤ)

/-- A YES parameter `ω₊ = ((π_p)_{p ∈ [N]}, h_A, h_B)`. -/
abbrev YESParam (k : ℕ) := (PIdx k → Equiv.Perm (HVtx k)) × SignFn k × SignFn k

noncomputable instance (k : ℕ) : Fintype (YESParam k) := instFintypeProd _ _
noncomputable instance (k : ℕ) : DecidableEq (YESParam k) := instDecidableEqProd

/-- The YES instance: `π_p` and the sign `σ_p(x) = χ(x)χ(π_p(x))`. Every parameter has positive
probability under `𝒟₊` (independent uniform permutations and signs), so `supp 𝒟₊` is the set of
all YES parameters. -/
def yesInst {k : ℕ} (ω : YESParam k) : SignedInstance k (3 * k) where
  perm := ω.1
  bit p x := decide (chi ω.2.1 ω.2.2 x * chi ω.2.1 ω.2.2 (ω.1 p x) = -1)

/-- A NO parameter `ω₋ = ((π_p)_{p ∈ [N]}, h_A, h_B, θ)`. -/
abbrev NOParam (k : ℕ) := (PIdx k → Equiv.Perm (HVtx k)) × SignFn k × SignFn k × Labeling k

noncomputable instance (k : ℕ) : Fintype (NOParam k) := instFintypeProd _ _
noncomputable instance (k : ℕ) : DecidableEq (NOParam k) := instDecidableEqProd

/-- `ω₋ ∈ supp 𝒟₋`: every `π_p` preserves the blocks of `θ`. -/
def InSuppNo {k : ℕ} (ω : NOParam k) : Prop :=
  ∀ p x, SameBlock ω.2.2.2 x (ω.1 p x)

/-- The NO instance: `π_p` and `σ_p(x) = χ(x)χ(y)s_θ(x, y)` with `y = π_p(x)`. -/
noncomputable def noInst {k : ℕ} (ω : NOParam k) : SignedInstance k (3 * k) where
  perm := ω.1
  bit p x := decide (chi ω.2.1 ω.2.2.1 x * chi ω.2.1 ω.2.2.1 (ω.1 p x) *
    sθ ω.2.2.2 x (ω.1 p x) = -1)

/-- `K = |𝒞| = N²`. -/
noncomputable def KK (k : ℕ) : ℝ := ((2 : ℝ) ^ k) ^ 2

/-- `μ = N³/K = N`. -/
noncomputable def mu (k : ℕ) : ℝ := (2 : ℝ) ^ k

/-- `ε₀ = 1/40`. -/
noncomputable def eps0 : ℝ := 1 / 40

/-- `|C_I^A(θ)| = |{x_A : c_A(x_A) = I}|`. -/
noncomputable def classA {k : ℕ} (θ : Labeling k) (I : LPair k) : ℕ :=
  (Finset.univ.filter (fun xA => θ.1 xA = I)).card

/-- `|C_I^B(θ)| = |{x_B : c_B(x_B) = I}|`. -/
noncomputable def classB {k : ℕ} (θ : Labeling k) (I : LPair k) : ℕ :=
  (Finset.univ.filter (fun xB => θ.2 xB = I)).card

/-- Balanced labelings, Equation (4): `(1 − ε₀)μ ≤ |C_I^P(θ)| ≤ (1 + ε₀)μ` for every `P ∈ {A, B}`
and `I ∈ 𝒞`. -/
def InThetaSize {k : ℕ} (θ : Labeling k) : Prop :=
  ∀ I : LPair k,
    (1 - eps0) * mu k ≤ classA θ I ∧ (classA θ I : ℝ) ≤ (1 + eps0) * mu k ∧
    (1 - eps0) * mu k ≤ classB θ I ∧ (classB θ I : ℝ) ≤ (1 + eps0) * mu k

/-- The permutation tuples allowed by `θ` (every `π_p` preserves every block). Conditioned on
`θ`, the permutations of `𝒟₋` are uniform on this set. -/
noncomputable def blockPerms {k : ℕ} (θ : Labeling k) :
    Finset (PIdx k → Equiv.Perm (HVtx k)) :=
  Finset.univ.filter (fun π => ∀ p x, SameBlock θ x (π p x))

/-- `Γ̄ = 𝔼[Γ | c_A, c_B, h_A, h_B]`: the signed adjacency matrix averaged over the blockwise
uniform permutations, with `θ, h_A, h_B` fixed (proof of Proposition 5.3, p. 22). -/
noncomputable def GamBar {k : ℕ} (θ : Labeling k) (hA hB : SignFn k) :
    Matrix (HVtx k) (HVtx k) ℂ :=
  (1 / ((blockPerms θ).card : ℂ)) • ∑ π ∈ blockPerms θ, (noInst (π, hA, hB, θ)).GamAvg

/-- A **good** NO parameter (start of Section 6, p. 24): it lies in `supp 𝒟₋`, satisfies the
class-size condition (4), and the graph-concentration condition `‖Γ − Γ̄‖ ≤ 1/8` (operator norm)
of the proof of Proposition 5.3. -/
def IsGood {k : ℕ} (ω : NOParam k) : Prop :=
  InSuppNo ω ∧ InThetaSize ω.2.2.2 ∧
    ‖(noInst ω).GamAvg - GamBar ω.2.2.2 ω.2.1 ω.2.2.1‖ ≤ 1 / 8

/-- `Pr_{θ ∼ ν}[E(θ)]` for the uniform (product) distribution `ν` of pair-labelings. -/
noncomputable def probLabeling {k : ℕ} (E : Labeling k → Prop) : ℝ :=
  ((Finset.univ.filter E).card : ℝ) / (Fintype.card (Labeling k) : ℝ)

/-- `Pr_{ω ∼ 𝒟₋}[E(ω)]`: `θ` uniform, `h_A, h_B` uniform and independent, and, given `θ`, the
permutation tuple uniform on `blockPerms θ` (independent blockwise uniform permutations). -/
noncomputable def probNo {k : ℕ} (E : NOParam k → Prop) : ℝ :=
  ∑ θ : Labeling k, ∑ hA : SignFn k, ∑ hB : SignFn k,
    (1 / (Fintype.card (Labeling k) : ℝ)) * (1 / (Fintype.card (SignFn k) : ℝ)) *
      (1 / (Fintype.card (SignFn k) : ℝ)) *
      (((blockPerms θ).filter (fun π => E (π, hA, hB, θ))).card : ℝ) /
        ((blockPerms θ).card : ℝ)

/-! ## The four-register antisymmetric projector and `h_Sep` -/

/-- `⟨i₁ i₂ | ⟨i₃ i₄| Alt_Q⟩` for a four-element set `Q ⊆ [N]`, Equation (3): `sgn/√24` when
`(i₁, i₂, i₃, i₄)` is an ordering of `Q` (the sign of the permutation producing that ordering
from the sorted `q₁ < q₂ < q₃ < q₄`), `0` otherwise. Registers 1, 2 form side `A`, 3, 4 side `B`. -/
noncomputable def altQ (N : ℕ) (Q : Finset (Fin N))
    (i : (Fin N × Fin N) × (Fin N × Fin N)) : ℂ :=
  let f : Fin 4 → ℕ := ![i.1.1.val, i.1.2.val, i.2.1.val, i.2.2.val]
  if Function.Injective f ∧ ({i.1.1, i.1.2, i.2.1, i.2.2} : Finset (Fin N)) = Q then
    (sortSign f : ℂ) / (Real.sqrt 24 : ℂ)
  else 0

/-- `P_N = Σ_{Q ∈ ([N] choose 4)} |Alt_Q⟩⟨Alt_Q|` on `(ℂ^N)^{⊗4}`. -/
noncomputable def projAlt (N : ℕ) :
    Matrix ((Fin N × Fin N) × (Fin N × Fin N)) ((Fin N × Fin N) × (Fin N × Fin N)) ℂ :=
  ∑ Q ∈ (Finset.univ : Finset (Fin N)).powersetCard 4,
    Matrix.vecMulVec (altQ N Q) (star (altQ N Q))

/-- `h_Sep(M) = max_{‖α‖ = ‖β‖ = 1} ⟨α ⊗ β| M |α ⊗ β⟩` over unit `α, β ∈ ℂ^ι`. -/
noncomputable def hSep {ι : Type*} [Fintype ι] (M : Matrix (ι × ι) (ι × ι) ℂ) : ℝ :=
  sSup {e | ∃ α β : ι → ℂ, IsUnit' α ∧ IsUnit' β ∧
    e = expect M (fun i => α i.1 * β i.2)}

end QMA2ClassicalSep.Main


