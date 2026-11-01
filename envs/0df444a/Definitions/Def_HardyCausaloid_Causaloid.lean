-- Prove2me | Definitions.Def_HardyCausaloid_Causaloid
-- name    : HardyCausaloid_Causaloid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:18:29.746851+00:00
-- url     : https://prove2.me/theorems/02407ae7-450f-4adb-8b90-2908ac37bd35
-- title:
--   The causaloid as the list (30) of $\Lambda$ matrices, and the vectors $\mathbf r_\alpha(R_O)$ it computes
-- statement:
--   A **causaloid** consists of
--
--   1. for each location $x$, a finite set $\Omega_x$ of labels at $x$ and a matrix $\Lambda^{l_x}_{\alpha_x}$ ($l_x\in\Omega_x$, $\alpha_x$ any label at $x$), eq. (17);
--   2. for each finite set $O$ of locations, a finite set $\Omega_O\subseteq\prod_{x\in O}\Omega_x$ and a matrix $\Lambda^{k}_{l}$ with $l\in\prod_{x\in O}\Omega_x$ and $k\in\Omega_O$, eqs. (28)–(29).
--
--   It refers to no model. From it the **causaloid product** computes, for each label $\alpha$ of $R_O$, the vector
--   $$\big(\mathbf r_\alpha(R_O)\big)_k=\sum_{l\in\prod_{x\in O}\Omega_x}\Big(\prod_{x\in O}\Lambda^{l_x}_{\alpha_x}\Big)\Lambda^{k}_{l}\qquad(26),$$
--   and for two regions with a matrix $\Lambda^{k_1k_2}_{l_1l_2}$ the product $(\mathbf u\otimes^{\Lambda}\mathbf v)_{k}=\sum_{l_1,l_2}u_{l_1}v_{l_2}\Lambda^{k}_{l_1l_2}$ of (26)–(27).
--
--   $C$ **is a causaloid of the model $M$** when $\Omega_x$ is a fiducial set of the elementary region $R_x$ with $\Lambda^{\cdot}_{\alpha_x}=\mathbf r_{\alpha_x}(R_x)$ as in (15); $\Omega_O$ is a fiducial set of $R_O$; and $p_\alpha=\mathbf r_\alpha(R_O)\cdot\mathbf p(R_O)$ for every region, label and preparation (eq. (20)).
--
--   The causaloid is the central object of the paper: knowing it is meant to be knowing everything the theory can calculate.
--
--   **Formalization Note** The causaloid is taken to be the list (30) itself; (31)'s further compression "(subset of Λ's | RULES)" leaves its RULES unspecified and is used only through the list it reproduces. (30)'s lower-case $\lambda$ is the same object as $\Lambda$.
-- source:
--   Hardy, Towards Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal Structure, arXiv:gr-qc/0608043v1, §4.2, eq. (17), p.12; §4.3, eqs. (25)–(29), pp.13–14; §4.4, eq. (30), p.14

import Mathlib
import Definitions.Def_HardyCausaloid_Model
import Definitions.Def_HardyCausaloid_Region
import Definitions.Def_HardyCausaloid_Fiducial

set_option autoImplicit false

namespace HardyCausaloid

universe u v w

/-- **The causaloid product of two regions**, Hardy, arXiv:gr-qc/0608043v1, §4.3, eqs. (26)–(27),
p.14: for a matrix `Λ^{k₁k₂}_{l₁l₂}` (`Λ l₁ l₂ k`, `l₁ ∈ Ω₁`, `l₂ ∈ Ω₂`, `k ∈ Ω₁₂`) and vectors
`u ∈ ℝ^{Ω₁}`, `v ∈ ℝ^{Ω₂}`, `(u ⊗^Λ v)_k = Σ_{l₁ l₂} u_{l₁} v_{l₂} Λ^{k}_{l₁l₂}`. -/
def causaloidProduct {ι₁ : Type u} {ι₂ : Type v} {κ : Type w} [Fintype ι₁] [Fintype ι₂]
    (Λ : ι₁ → ι₂ → κ → ℝ) (u : ι₁ → ℝ) (v' : ι₂ → ℝ) : κ → ℝ :=
  fun k => ∑ l₁, ∑ l₂, u l₁ * v' l₂ * Λ l₁ l₂ k

/-- **The causaloid**, as the list (30) of Λ matrices, Hardy, arXiv:gr-qc/0608043v1, §4.2,
eq. (17), p.12, §4.3, eqs. (25), (28)–(29), pp.13–14, and §4.4, eq. (30), p.14.

* `Ω₁ x` is a finite set of labels at `x` (the elementary fiducial set) and `Λ₁ x α l` is
  `Λ^{l_x}_{α_x}` of (17) and (30), the first-level compression matrix;
* `ΩC O`, for every finite set `O` of locations, is a finite set of families `k = (k_x)_{x∈O}`
  with `k_x ∈ Ω₁ x`, i.e. a subset of `∏_{x∈O} Ω₁ x` (the fiducial set `Ω_{12…n}` of (28)), and
  `Λ O l k` is `Λ^{k}_{l}` of (29) and (30), for `l ∈ ∏_{x∈O} Ω₁ x` and `k ∈ ΩC O`.

The structure refers to no model: it is data from which vectors are computed (`Causaloid.r`).

**Formalization Note** The causaloid is taken to be the list (30) itself; (31)'s further
compression "(subset of Λ's | RULES)" leaves its RULES unspecified, and any such compression is
used only through the list it reproduces. (30)'s lower-case `λ` is the same object as `Λ`. -/
structure Causaloid {X : Type u} (Setting : X → Type v) (Outcome : (x : X) → Setting x → Type w)
    where
  /-- The elementary fiducial set `Ω_x`. -/
  Ω₁ : ∀ x, Finset (Label Setting Outcome x)
  /-- `Λ^{l_x}_{α_x}`, eq. (17). -/
  Λ₁ : ∀ x, Label Setting Outcome x → Ω₁ x → ℝ
  /-- The fiducial set of the region of `O`, a subset of `∏_{x∈O} Ω_x`, eq. (28). -/
  ΩC : ∀ O : Finset X, Finset (∀ x : O, Ω₁ x.1)
  /-- `Λ^{k}_{l}` for the region of `O`, eq. (29). -/
  Λ : ∀ O : Finset X, (∀ x : O, Ω₁ x.1) → ΩC O → ℝ

variable {X : Type u} {Setting : X → Type v} {Outcome : (x : X) → Setting x → Type w}

namespace Causaloid

/-- The label of the region of `O` named by a family `k ∈ ∏_{x∈O} Ω_x`. -/
def embed (C : Causaloid Setting Outcome) (O : Finset X) (k : ∀ x : O, C.Ω₁ x.1) :
    Lab Setting Outcome O :=
  fun x => (k x).1

theorem embed_injective (C : Causaloid Setting Outcome) (O : Finset X) :
    Function.Injective (C.embed O) := by
  intro k k' h
  funext x
  exact Subtype.ext (congrFun h x)

/-- The fiducial set `ΩC O` as a finite set of labels of the region of `O`. -/
def fidSet (C : Causaloid Setting Outcome) (O : Finset X) : Finset (Lab Setting Outcome O) :=
  (C.ΩC O).map ⟨C.embed O, C.embed_injective O⟩

variable [DecidableEq X]

/-- **The vector `r_α` computed from the causaloid**, Hardy, arXiv:gr-qc/0608043v1, §4.3,
eq. (26), p.14, for `n` regions (eqs. (28)–(29)) and §4.5, p.16 ("using Λ^{lx}_{αx} from first
level physical compression to get the components of the r_{αx}(Rx) vectors for the elementary
regions to get us started"):
`r_α(R_O)_k = Σ_{l ∈ ∏_{x∈O} Ω_x} (∏_{x∈O} Λ^{l_x}_{α_x}) Λ^{k}_{l}` for `k ∈ ΩC O`. -/
def r (C : Causaloid Setting Outcome) (O : Finset X) (α : Lab Setting Outcome O) :
    C.ΩC O → ℝ :=
  fun k => ∑ l : (∀ x : O, C.Ω₁ x.1), (∏ x : O, C.Λ₁ x.1 (α x) (l x)) * C.Λ O l k

/-- **The state of the region of `O` on the causaloid's fiducial set**, Hardy,
arXiv:gr-qc/0608043v1, §4.3, eq. (19), p.12: `p(R_O)_k = p_k` for `k ∈ ΩC O`, under the
generalised preparation `s`. -/
def state (M : Model Setting Outcome) (C : Causaloid Setting Outcome) (O : Finset X)
    (s : ∀ x, Label Setting Outcome x) : C.ΩC O → ℝ :=
  fun k => regionTable M O (C.embed O k.1) s

end Causaloid

/-- **`C` is a causaloid of the model `M`**, Hardy, arXiv:gr-qc/0608043v1, §4.2 (eqs. (14)–(17),
pp.11–12), §4.3 (eqs. (19)–(20), (25)–(29), pp.12–14) and §4.4 (eq. (30), p.14):

1. for every location `x`, `C.Ω₁ x` is a fiducial set of the elementary region `R_x`, and
   `C.Λ₁ x α` is the vector `r_α(R_x)` of (15): `p_α = Σ_{l ∈ Ω_x} Λ^{l}_{α} p_l` for every
   preparation;
2. for every finite set `O`, `C.ΩC O` is a fiducial set of the region `R_O`;
3. for every `O`, every label `α` of `R_O` and every preparation `s`, the vector computed by the
   causaloid product gives the probability: `p_α = r_α(R_O) · p(R_O)` (eq. (20)). -/
structure IsCausaloidOf [DecidableEq X] (C : Causaloid Setting Outcome) (M : Model Setting Outcome) :
    Prop where
  elem_fiducial : ∀ x, Fiducial (elemTable M x) (C.Ω₁ x)
  elem_eq : ∀ x α s, elemTable M x α s = C.Λ₁ x α ⬝ᵥ stateVec (elemTable M x) (C.Ω₁ x) s
  region_fiducial : ∀ O, Fiducial (regionTable M O) (C.fidSet O)
  region_eq : ∀ O α s, regionTable M O α s = C.r O α ⬝ᵥ C.state M O s

end HardyCausaloid


