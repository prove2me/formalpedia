-- Prove2me | Definitions.Def_ConstGapCircuits_triangleGap
-- name    : ConstGapCircuits_triangleGap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:53:05.503395+00:00
-- url     : https://prove2.me/theorems/950f72b9-7305-4c75-9b1d-38a222c8c44e
-- title:
--   Closed angle groups and the triangle Hamiltonian gap (3.1)–(3.3)
-- statement:
--   Let $\Theta\le\mathbb R/2\pi\mathbb Z$ be any closed additive subgroup and let $n\ge1$. The group $G_\Theta$ is generated topologically by all $e^{i\theta P}$ for $P\in\mathcal P_n$ and $\theta\in\Theta$. The group $L_\Theta$ uses only the three Pauli axes on the first qubit. When $\Theta$ is discrete, both groups also contain the full ambient centre, and each angle projector averages that centre. Thus
--   $$\Pi(\rho|\Theta,P)=\int_{Z\cdot\exp(i\Theta P)}\rho(h)\,d\mu(h)$$
--   in the discrete case; the central factor is omitted for the full circle. Define
--   $$H_0(\rho)=\sum_{a\in\{x,y,z\}}(I-\Pi(\rho|\Theta,\sigma_0^a)),\qquad
--   \Delta_\Theta=\sup\{c\in[0,3]:\ \forall\rho,\ H_0(\rho)^2\succeq cH_0(\rho)\}.$$
--
--   The supremum is bounded and contains zero. This supplies the model for triangle counting and both single-qubit gap calculations. The group is one-qubit, as indicated by the inclusion in SU(2) and Lemma 3.10, despite the text's LU(2) label. Central averaging follows the explicit convention in the proof of Theorem 3.12.
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 18–20, §3, (3.1)–(3.3), and the proof of Theorem 3.12

import Definitions.Def_ConstGapCircuits_walks

noncomputable section

namespace ConstGapCircuits
open scoped BigOperators ComplexOrder
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Three Pauli axes on qubit zero; n≥1 is imposed on every result using this. -/
def axisString (n : ℕ) (a : Fin 3) : Fin n → Fin 4 :=
  fun j => if j.val = 0 then ⟨a.val + 1, by omega⟩ else 0

/-- The group G_Theta of §3, with central phases for discrete Theta. -/
def thetaGlobal (n : ℕ) (Θ : Angles) : ClosedSubgroup (SU n) :=
  closedGenerated {U | (∃ p : PauliIndex n, ∃ θ : ℝ,
    (θ : AngleGroup) ∈ Θ ∧ (U : Mat n) = rotation p.val θ) ∨
    (DiscreteTopology Θ ∧ U ∈ Subgroup.center (SU n))}

/-- The one-qubit group L_Theta inside SU(2^n). -/
def thetaLocal (n : ℕ) (Θ : Angles) : ClosedSubgroup (SU n) :=
  closedGenerated {U | (∃ a : Fin 3, ∃ θ : ℝ,
    (θ : AngleGroup) ∈ Θ ∧ (U : Mat n) = rotation (axisString n a) θ) ∨
    (DiscreteTopology Θ ∧ U ∈ Subgroup.center (SU n))}

abbrev ThetaGlobal (n : ℕ) (Θ : Angles) : Type := {U : SU n // U ∈ thetaGlobal n Θ}
abbrev ThetaLocal (n : ℕ) (Θ : Angles) : Type := {U : SU n // U ∈ thetaLocal n Θ}

instance thetaGlobalCompact (n : ℕ) (Θ : Angles) : CompactSpace (ThetaGlobal n Θ) :=
  isCompact_iff_compactSpace.mp (thetaGlobal n Θ).isClosed'.isCompact
instance thetaLocalCompact (n : ℕ) (Θ : Angles) : CompactSpace (ThetaLocal n Θ) :=
  isCompact_iff_compactSpace.mp (thetaLocal n Θ).isClosed'.isCompact

instance thetaGlobalTopologicalGroup (n : ℕ) (Θ : Angles) : IsTopologicalGroup (ThetaGlobal n Θ) where
  continuous_mul := continuous_induced_rng.mpr ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd))
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.inv
instance thetaLocalTopologicalGroup (n : ℕ) (Θ : Angles) : IsTopologicalGroup (ThetaLocal n Θ) where
  continuous_mul := continuous_induced_rng.mpr ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd))
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.inv

def thetaGlobalInclusion (n : ℕ) (Θ : Angles) : ThetaGlobal n Θ →* SU n :=
  (thetaGlobal n Θ).toSubgroup.subtype

def thetaLocalInclusion (n : ℕ) (Θ : Angles) : ThetaLocal n Θ →* SU n :=
  (thetaLocal n Θ).toSubgroup.subtype

def triangleHamiltonian (n : ℕ) (Θ : Angles) (ρ : UnitaryRep (ThetaLocal n Θ)) :
    Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ :=
  ∑ a : Fin 3, (1 - subgroupProjector
    (thetaSubgroup (G := ThetaLocal n Θ) (thetaLocalInclusion n Θ) Θ (axisString n a)) ρ)

/-- Equations (3.2),(3.3): a bounded, nonempty supremum of positive-semidefinite inequalities. -/
def thetaGap (n : ℕ) (Θ : Angles) : ℝ :=
  sSup {c : ℝ | c ∈ Set.Icc 0 3 ∧ ∀ ρ : UnitaryRep (ThetaLocal n Θ),
    Matrix.PosSemidef ((triangleHamiltonian n Θ ρ) ^ 2 - c • triangleHamiltonian n Θ ρ)}

def thetaPauliAverage (n : ℕ) (Θ : Angles) (ρ : UnitaryRep (ThetaGlobal n Θ)) :=
  (Fintype.card (PauliIndex n) : ℂ)⁻¹ • ∑ p : PauliIndex n,
    subgroupProjector (thetaSubgroup (G := ThetaGlobal n Θ) (thetaGlobalInclusion n Θ) Θ p.val) ρ

end ConstGapCircuits


