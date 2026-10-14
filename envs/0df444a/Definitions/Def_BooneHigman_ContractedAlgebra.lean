-- Prove2me | Definitions.Def_BooneHigman_ContractedAlgebra
-- name    : BooneHigman_ContractedAlgebra
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-14T10:16:59.653209+00:00
-- url     : https://prove2.me/theorems/a1d3dd90-8feb-4a8b-a6f3-e7434bdb06e6
-- title:
--   The contracted monoid algebra $k_0[D]$ (Section 6.2)
-- statement:
--   For a monoid $D$ with zero $\Omega \neq 1_D$, the contracted monoid algebra $k_0[D]$ over $k = \mathbb{F}_2$, from Section 6.2 of OpenAI's "Finite algebraic envelopes and the Boone-Higman conjecture" preprint: the group algebra $\mathbb{F}_2[D]$ with the basis vector at $\Omega$ identified with the algebra zero, realized here via the idempotent-corner construction ($e_\Omega$, the basis vector of $\Omega$, is a nonzero central idempotent of $\mathbb{F}_2[D]$ since $\Omega$ is absorbing, so $1 - e_\Omega$ is too, and its corner $(1-e_\Omega)R(1-e_\Omega)$ is a unital ring in which $e_\Omega$ has become $0$). The embedding `toContracted : D \to k_0[D]` sends $d$ to the class of its basis vector; it sends $\Omega \mapsto 0$, $1_D \mapsto 1$, and is multiplicative (`toContracted_zero`, `toContracted_one`, `toContracted_mul`), and every element of $k_0[D]$ is a finite $\mathbb{F}_2$-linear combination of `toContracted d`'s (`toContracted_eq_sum`) — the basis-decomposition fact used to prove $k_0[D]$ is simple when $D$ has the finite-tuple selector property of Theorem 6.2(iii).
-- source:
--   OpenAI, "Finite algebraic envelopes and the Boone-Higman conjecture", OpenAI Math Release, 2026-09-23, Section 6.2 (the construction preceding Lemma 6.3).

import Mathlib

/-!
The contracted monoid algebra `k0[D]` of a monoid `D` with zero `Ω ≠ 1_D` (Section 6.2 of
OpenAI's "Finite algebraic envelopes and the Boone-Higman conjecture" preprint, `k = F2`):
`MonoidAlgebra (ZMod 2) D` with the basis vector at `Ω` identified with the algebra zero.
Realized via the idempotent-corner machinery (`Mathlib.RingTheory.Idempotents`): `e_Ω :=
MonoidAlgebra.of (ZMod 2) D Ω` is a nonzero CENTRAL idempotent (since `Ω` is absorbing), so
`1 - e_Ω` is too, and its corner `(1-e_Ω) R (1-e_Ω)` is a ring with identity `1 - e_Ω` in which
`e_Ω` (hence the basis vector at `Ω`) has become `0`.
-/

variable {D : Type*} [MonoidWithZero D]

noncomputable def eZero : MonoidAlgebra (ZMod 2) D := MonoidAlgebra.of (ZMod 2) D 0

theorem eZero_idem : IsIdempotentElem (eZero (D := D)) := by
  show eZero * eZero = eZero
  unfold eZero
  rw [← map_mul, zero_mul]

theorem eZero_comm (a : MonoidAlgebra (ZMod 2) D) : Commute (eZero (D := D)) a :=
  MonoidAlgebra.of_commute (fun m' => by show (0 : D) * m' = m' * 0; rw [zero_mul, mul_zero]) a

theorem eZero_left_assoc (b c : MonoidAlgebra (ZMod 2) D) :
    eZero (D := D) * (b * c) = eZero * b * c :=
  (_root_.mul_assoc eZero b c).symm

theorem eZero_right_assoc (a b : MonoidAlgebra (ZMod 2) D) :
    a * b * eZero (D := D) = a * (b * eZero) :=
  _root_.mul_assoc a b eZero

theorem eZero_central : IsMulCentral (eZero (D := D)) :=
  ⟨eZero_comm, eZero_left_assoc, eZero_right_assoc⟩

theorem oneSubEZero_idem : IsIdempotentElem ((1 : MonoidAlgebra (ZMod 2) D) - eZero) :=
  eZero_idem.one_sub

/-- The contracted monoid algebra `k0[D]`. -/
noncomputable abbrev ContractedAlgebra (D : Type*) [MonoidWithZero D] : Type _ :=
  (oneSubEZero_idem (D := D)).Corner

noncomputable def toContracted (d : D) : ContractedAlgebra D :=
  ⟨(1 - eZero) * MonoidAlgebra.of (ZMod 2) D d * (1 - eZero), ⟨MonoidAlgebra.of (ZMod 2) D d, rfl⟩⟩

theorem toContracted_val (d : D) :
    (toContracted d).val =
      (1 - eZero) * MonoidAlgebra.of (ZMod 2) D d * (1 - eZero) := rfl

theorem eZero_mul_of (d : D) : eZero (D := D) * MonoidAlgebra.of (ZMod 2) D d = eZero := by
  show MonoidAlgebra.of (ZMod 2) D 0 * MonoidAlgebra.of (ZMod 2) D d = MonoidAlgebra.of (ZMod 2) D 0
  rw [← map_mul, zero_mul]

theorem of_mul_oneSubEZero (d : D) :
    MonoidAlgebra.of (ZMod 2) D d * (1 - eZero) = MonoidAlgebra.of (ZMod 2) D d - eZero := by
  rw [mul_sub, mul_one]
  congr 1
  show MonoidAlgebra.of (ZMod 2) D d * MonoidAlgebra.of (ZMod 2) D 0 =
    MonoidAlgebra.of (ZMod 2) D 0
  rw [← map_mul, mul_zero]

theorem oneSubEZero_mul_of (d : D) :
    (1 - eZero) * MonoidAlgebra.of (ZMod 2) D d = MonoidAlgebra.of (ZMod 2) D d - eZero := by
  rw [sub_mul, one_mul]
  congr 1
  exact eZero_mul_of d

/-- The identification `toContracted d = (\text{basis vector of } d) - e_\Omega`, valid for
EVERY `d` (including `d = 0`, where it gives `0`). -/
theorem toContracted_eq (d : D) :
    (toContracted d).val = MonoidAlgebra.of (ZMod 2) D d - eZero := by
  rw [toContracted_val, oneSubEZero_mul_of, sub_mul, of_mul_oneSubEZero,
    eZero_idem.mul_one_sub_self, sub_zero]

theorem toContracted_zero : toContracted (0 : D) = 0 := by
  apply Subtype.ext
  show (toContracted (0:D)).val = (0 : MonoidAlgebra (ZMod 2) D)
  rw [toContracted_eq, show MonoidAlgebra.of (ZMod 2) D (0:D) = eZero from rfl, sub_self]

theorem of_mul_eZero (d : D) : MonoidAlgebra.of (ZMod 2) D d * eZero = eZero := by
  show MonoidAlgebra.of (ZMod 2) D d * MonoidAlgebra.of (ZMod 2) D 0 = MonoidAlgebra.of (ZMod 2) D 0
  rw [← map_mul, mul_zero]

theorem toContracted_mul (d d' : D) :
    toContracted (d * d') = toContracted d * toContracted d' := by
  apply Subtype.ext
  show (toContracted (d * d')).val = (toContracted d).val * (toContracted d').val
  rw [toContracted_eq, toContracted_eq, toContracted_eq, sub_mul, mul_sub, mul_sub,
    of_mul_eZero, eZero_mul_of, eZero_idem.eq, map_mul]
  abel

theorem monoidAlgebra_eq_sum_single (r : MonoidAlgebra (ZMod 2) D) :
    r = r.coeff.sum (fun d c => MonoidAlgebra.single d c) := by
  conv_lhs =>
    rw [← MonoidAlgebra.coeffAddEquiv.symm_apply_apply r, MonoidAlgebra.coeffAddEquiv_apply,
      ← Finsupp.sum_single r.coeff]
  show MonoidAlgebra.coeffAddEquiv.symm (∑ a ∈ r.coeff.support, Finsupp.single a (r.coeff a)) = _
  rw [map_sum]
  rfl

theorem corner_map_sum (r : MonoidAlgebra (ZMod 2) D) :
    (1 - eZero) * r * (1 - eZero) =
      r.coeff.sum (fun d c => (1 - eZero) * MonoidAlgebra.single d c * (1 - eZero)) := by
  conv_lhs => rw [monoidAlgebra_eq_sum_single r]
  show (1 - eZero) * (∑ d ∈ r.coeff.support, MonoidAlgebra.single d (r.coeff d)) * (1 - eZero) = _
  rw [Finset.mul_sum, Finset.sum_mul]
  rfl

theorem single_eq_smul_of (d : D) (c : ZMod 2) :
    MonoidAlgebra.single d c = c • MonoidAlgebra.of (ZMod 2) D d := by
  rw [MonoidAlgebra.of_apply]
  ext d'
  simp [Finsupp.smul_single]

theorem corner_single_eq_smul (d : D) (c : ZMod 2) :
    (1 - eZero) * MonoidAlgebra.single d c * (1 - eZero) = c • (toContracted d).val := by
  rw [single_eq_smul_of, mul_smul_comm, smul_mul_assoc, toContracted_val]

/-- Every corner element is a finite `F2`-combination of `toContracted d`'s. -/
theorem toContracted_eq_sum (a : ContractedAlgebra D) :
    a.val = a.val.coeff.sum (fun d c => c • (toContracted d).val) := by
  have h1 := ((Subsemigroup.mem_corner_iff oneSubEZero_idem).mp a.2).1
  have h2 := ((Subsemigroup.mem_corner_iff oneSubEZero_idem).mp a.2).2
  have hcorner : (1 - eZero) * a.val * (1 - eZero) = a.val := by rw [h1, h2]
  conv_lhs => rw [← hcorner, corner_map_sum]
  apply Finsupp.sum_congr
  intro d _
  exact corner_single_eq_smul d (a.val.coeff d)

theorem toContracted_one : toContracted (1 : D) = 1 := by
  apply Subtype.ext
  show (toContracted (1:D)).val = (1 : ContractedAlgebra D).val
  rw [toContracted_eq, map_one]
  rfl


