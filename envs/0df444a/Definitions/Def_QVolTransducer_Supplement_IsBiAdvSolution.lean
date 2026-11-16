-- Prove2me | Definitions.Def_QVolTransducer_Supplement_IsBiAdvSolution
-- name    : QVolTransducer_Supplement_IsBiAdvSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:31:39.143483+00:00
-- url     : https://prove2.me/theorems/ebadbeab-43c6-4505-9a11-466b3ac2df68
-- title:
--   Feasible solutions to the unidirectional and bidirectional adversary bounds
-- statement:
--   A **state-conversion problem** $P=\{(|\sigma_x\rangle,|\tau_x\rangle,O_x)\}_{x\in\mathcal D}$ consists of input states $|\sigma_x\rangle\in\mathcal V_I$, target states $|\tau_x\rangle\in\mathcal V_O$ and oracles $O_x\in\mathcal U(\mathcal H)$, indexed by an arbitrary set $\mathcal D$. Let $\mathcal W$ be a Hilbert space. A **feasible solution to the unidirectional adversary bound** is a family $\{|w_x\rangle\}_{x\in\mathcal D}\subseteq\mathcal H\otimes\mathcal W$ with
--
--   $$\langle w_x|\big((I_{\mathcal H}-O_x^\dagger O_y)\otimes I_{\mathcal W}\big)|w_y\rangle=\langle\sigma_x|\sigma_y\rangle-\langle\tau_x|\tau_y\rangle\qquad\text{for all }x,y\in\mathcal D,$$
--
--   and a **feasible solution to the bidirectional adversary bound** is a family of pairs $\{|w_x^+\rangle,|w_x^-\rangle\}_{x\in\mathcal D}\subseteq\mathcal H\otimes\mathcal W$ with
--
--   $$\langle w_x^+|\big((I_{\mathcal H}-O_x^\dagger O_y)\otimes I_{\mathcal W}\big)|w_y^-\rangle=\langle\sigma_x|\sigma_y\rangle-\langle\tau_x|\tau_y\rangle\qquad\text{for all }x,y\in\mathcal D.$$
--
--   Its **cost** is $\sup_{x\in\mathcal D}\max\{\|w_x^+\|^2,\|w_x^-\|^2\}$, and $\overleftrightarrow{\mathrm{ADV}}(P)$ is the least cost over all workspaces and feasible solutions.
--
--   These notions connect query complexity with transducers: canonical transducers yield feasible solutions (Theorem 2.12) and conversely.
--
--   **Formalization Note** The oracle space is $\mathbb C^H$ for a finite type $H$; $\mathbb C^H\otimes\mathcal W$ is modelled as the $L^2$-sum of $|H|$ copies of $\mathcal W$ (`PiLp 2`), and the form $\langle v|((I-O^\dagger O')\otimes I)|w\rangle$ is $\sum_{h,h'}(I-O^\dagger O')_{hh'}\langle v_h|w_{h'}\rangle$. The workspace $\mathcal W$ is any complex inner-product space. The cost is a supremum in $[0,\infty]$ (the paper's maximum need not be attained for infinite $\mathcal D$). `curryHW` reads a coordinate vector of $\mathbb C^{H\times W}$ in $\mathbb C^H\otimes\mathbb C^W$.
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Definitions 2.1 and 2.2, p.11 (PDF p.13)

import Mathlib

namespace QVolTransducer.Supplement

open scoped ENNReal

/-- The tensor product `ℋ ⊗ 𝒲` of the oracle space `ℋ = ℂ^H` (a finite index type `H`) with a
workspace `𝒲` that may be any complex Hilbert space (Cornelissen, Apers, Gribling, *Improved quantum
volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of
November 3, 2026, sha256 40d7b52d…), Definition 2.2, p.11: "|w_x⟩ ∈ H ⊗ W, W Hilbert space").

**Formalization Note** `ℂ^H ⊗ 𝒲` is modelled as the `L²`-sum of `|H|` copies of `𝒲`, i.e.
`PiLp 2 (fun _ : H => 𝒲)`: a vector `v` is the family `(v_h)_{h ∈ H}` of its components
`v = Σ_h |h⟩ ⊗ v_h`. This is isometric to the Hilbert tensor product. -/
abbrev TensorW (H : Type*) (W : Type*) := PiLp 2 (fun _ : H => W)

/-- The sesquilinear form `⟨v| ((I_ℋ − O†O') ⊗ I_𝒲) |w⟩` on `ℂ^H ⊗ 𝒲` (arXiv:2609.40217,
Definition 2.2, p.11). With `v = Σ_h |h⟩ ⊗ v_h` and `w = Σ_h |h⟩ ⊗ w_h` it equals
`Σ_{h,h'} (I − O†O')_{h h'} ⟨v_h | w_{h'}⟩`. -/
noncomputable def advForm {H W : Type*} [Fintype H] [DecidableEq H] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (O O' : Matrix H H ℂ) (v w : TensorW H W) : ℂ :=
  ∑ h, ∑ h', ((1 : Matrix H H ℂ) - O.conjTranspose * O') h h' * inner ℂ (v h) (w h')

/-- A feasible solution to the **unidirectional adversary bound** of the state-conversion problem
`{(|σ_x⟩, |τ_x⟩, O_x)}_{x∈D}` (arXiv:2609.40217, Definitions 2.1 and 2.2, p.11): vectors
`|w_x⟩ ∈ ℋ ⊗ 𝒲` with
`⟨w_x| ((I_ℋ − O_x†O_y) ⊗ I_𝒲) |w_y⟩ = ⟨σ_x|σ_y⟩ − ⟨τ_x|τ_y⟩` for all `x, y ∈ D`.

**Formalization Note** The input states lie in a Hilbert space `V_I` and the target states in `V_O`
(Definition 2.1); the oracles are given as matrices on `ℂ^H` (unitarity is a hypothesis of every
statement that uses the notion). -/
def IsUniAdvSolution {D H W VI VO : Type*} [Fintype H] [DecidableEq H] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [NormedAddCommGroup VI] [InnerProductSpace ℂ VI]
    [NormedAddCommGroup VO] [InnerProductSpace ℂ VO]
    (σ : D → VI) (τ : D → VO) (O : D → Matrix H H ℂ) (w : D → TensorW H W) : Prop :=
  ∀ x y, advForm (O x) (O y) (w x) (w y) = inner ℂ (σ x) (σ y) - inner ℂ (τ x) (τ y)

/-- A feasible solution to the **bidirectional adversary bound** of the state-conversion problem
`{(|σ_x⟩, |τ_x⟩, O_x)}_{x∈D}` (arXiv:2609.40217, Definition 2.2, p.11): pairs of vectors
`|w_x^+⟩, |w_x^−⟩ ∈ ℋ ⊗ 𝒲` with
`⟨w_x^+| ((I_ℋ − O_x†O_y) ⊗ I_𝒲) |w_y^−⟩ = ⟨σ_x|σ_y⟩ − ⟨τ_x|τ_y⟩` for all `x, y ∈ D`. -/
def IsBiAdvSolution {D H W VI VO : Type*} [Fintype H] [DecidableEq H] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [NormedAddCommGroup VI] [InnerProductSpace ℂ VI]
    [NormedAddCommGroup VO] [InnerProductSpace ℂ VO]
    (σ : D → VI) (τ : D → VO) (O : D → Matrix H H ℂ) (wp wm : D → TensorW H W) : Prop :=
  ∀ x y, advForm (O x) (O y) (wp x) (wm y) = inner ℂ (σ x) (σ y) - inner ℂ (τ x) (τ y)

/-- The cost `sup_{x∈D} max{‖|w_x^+⟩‖², ‖|w_x^−⟩‖²}` of a feasible solution to the bidirectional
adversary bound (arXiv:2609.40217, Definition 2.2, p.11; `ADV↔(P)` is the least cost over all
workspaces and all feasible solutions).

**Formalization Note** The paper writes `max_{x∈D}`; for infinite `D` the maximum need not exist,
so the supremum is taken, in `ℝ≥0∞` (an unbounded family has cost `∞`, an empty one cost `0`). -/
noncomputable def biAdvCost {D H W : Type*} [Fintype H] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (wp wm : D → TensorW H W) : ℝ≥0∞ :=
  ⨆ x, max (ENNReal.ofReal (‖wp x‖ ^ 2)) (ENNReal.ofReal (‖wm x‖ ^ 2))

/-- A vector of the coordinate space `ℂ^(H × W)` read as a vector of `ℂ^H ⊗ ℂ^W`, the
identification used to compare the catalysts of a canonical transducer (Definition 2.10, p.14)
with feasible solutions of the adversary bound (Definition 2.2). -/
noncomputable def curryHW {H W : Type*} [Fintype H] [Fintype W]
    (w : EuclideanSpace ℂ (H × W)) : TensorW H (EuclideanSpace ℂ W) :=
  WithLp.toLp 2 (fun h => WithLp.toLp 2 (fun j => w (h, j)))

end QVolTransducer.Supplement


