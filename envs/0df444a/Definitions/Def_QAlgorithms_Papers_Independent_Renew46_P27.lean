-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P27
-- name    : QAlgorithms_Papers_Independent_Renew46_P27
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T20:52:15.269789+00:00
-- url     : https://prove2.me/theorems/c1a34448-8947-49ac-bc57-a99af02a8ed2
-- title:
--   Definitions for Non-abelian extensions of infinite-dimensional Lie groups
-- statement:
--   The objects the formalized statements of *Non-abelian extensions of infinite-dimensional Lie groups* (arXiv:math/0504295) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `NormalizedTwoCochain`: Definition I.1, PDF p. 5: normalization in degree two, with no smoothness condition. Both identity-coordinate conditions are retained.
--   - `CompatibleFactorData`: Equation (2.5), PDF p. 15: the compatibility equation S(g) S(h) = C_N(omega(g,h)) S(gh), evaluated on each element of N. The automorphisms are algebraic, as in the abstract C^1/C^2 lemma II.7.
--   - `nonabelianDifferential`: Lemma I.10(3), PDF p. 11, used by Lemma II.7 on PDF pp. 15–16: the ordered, multiplicative nonabelian degree-two differential.
--   - `IsFactorCocycle`: Lemma II.7, PDF p. 15: d_S omega = 1 means this equality at every triple.
--   - `extensionProduct`: Equation (2.1) and Lemma II.7, PDF pp. 14–15: the actual twisted multiplication on the product set. This is not the ambient product group law.
--   - `conjugationCochain`: Definition I.1, PDF p. 5, and equation (2.7), PDF p. 15: the ordered cochain omega_g(x) occurring in conjugation.
--   - `AdmitsExtensionGroup`: Lemma II.7, PDF p. 15: a group structure must have exactly the specified multiplication; an unrelated group instance on the same set is insufficient.
-- source:
--   Non-abelian extensions of infinite-dimensional Lie groups, arXiv:math/0504295v1, https://arxiv.org/abs/math/0504295v1

import Mathlib

/-!
Algebraic factor-system statements from Neeb, arXiv:math/0504295v1.
Only Lemma II.7 is stated. Other assigned nodes are explicitly deferred in
HARD.md and GAPS.json. No smooth classification is claimed by this module.
All definitions have complete bodies; only the source theorem uses sorry.
Compilation and independent moderation are pending the batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Renew46.P27

universe u v

variable {G : Type u} {N : Type v} [Group G] [Group N]

/-- Definition I.1, PDF p. 5: normalization in degree two, with no
smoothness condition. Both identity-coordinate conditions are retained. -/
def NormalizedTwoCochain (omega : G → G → N) : Prop :=
  (∀ g, omega 1 g = 1) ∧ (∀ g, omega g 1 = 1)

/-- Sanity: the constant identity cochain is normalized. -/
example : NormalizedTwoCochain (fun (_ _ : G) => (1 : N)) := by
  exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- Equation (2.5), PDF p. 15: the compatibility equation
S(g) S(h) = C_N(omega(g,h)) S(gh), evaluated on each element of N.
The automorphisms are algebraic, as in the abstract C^1/C^2 lemma II.7. -/
def CompatibleFactorData (S : G → MulAut N) (omega : G → G → N) : Prop :=
  ∀ g h n, S g (S h n) = omega g h * S (g * h) n * (omega g h)⁻¹

/-- Sanity: the trivial action and constant identity cochain are compatible. -/
example : CompatibleFactorData (fun (_ : G) => MulEquiv.refl N)
    (fun _ _ => (1 : N)) := by
  intro g h n
  simp

/-- Lemma I.10(3), PDF p. 11, used by Lemma II.7 on PDF pp. 15–16:
the ordered, multiplicative nonabelian degree-two differential. -/
def nonabelianDifferential (S : G → MulAut N) (omega : G → G → N)
    (g h k : G) : N :=
  S g (omega h k) * omega g (h * k) *
    (omega (g * h) k)⁻¹ * (omega g h)⁻¹

/-- Sanity: the identity cochain has trivial differential for any S. -/
example (S : G → MulAut N) (g h k : G) :
    nonabelianDifferential S (fun _ _ => 1) g h k = 1 := by
  simp [nonabelianDifferential]

/-- Lemma II.7, PDF p. 15: d_S omega = 1 means this equality at every triple. -/
def IsFactorCocycle (S : G → MulAut N) (omega : G → G → N) : Prop :=
  ∀ g h k, nonabelianDifferential S omega g h k = 1

/-- Sanity: no nontriviality assumption is needed for the trivial cocycle. -/
example (S : G → MulAut N) : IsFactorCocycle S (fun _ _ => 1) := by
  intro g h k
  simp [nonabelianDifferential]

/-- Equation (2.1) and Lemma II.7, PDF pp. 14–15: the actual twisted
multiplication on the product set. This is not the ambient product group law. -/
def extensionProduct (S : G → MulAut N) (omega : G → G → N)
    (a b : N × G) : N × G :=
  (a.1 * S a.2 b.1 * omega a.2 b.2, a.2 * b.2)

/-- Sanity: trivial factor data give the ordinary product multiplication. -/
example (a b : N × G) :
    extensionProduct (fun _ => MulEquiv.refl N) (fun _ _ => 1) a b =
      (a.1 * b.1, a.2 * b.2) := by
  simp [extensionProduct]

/-- Definition I.1, PDF p. 5, and equation (2.7), PDF p. 15:
the ordered cochain omega_g(x) occurring in conjugation. -/
def conjugationCochain (omega : G → G → N) (g x : G) : N :=
  omega g x * (omega (g * x * g⁻¹) g)⁻¹

/-- Sanity: the conjugation cochain is trivial for the identity two-cochain. -/
example (g x : G) : conjugationCochain (fun (_ _ : G) => (1 : N)) g x = 1 := by
  simp [conjugationCochain]

/-- Lemma II.7, PDF p. 15: a group structure must have exactly the specified
multiplication; an unrelated group instance on the same set is insufficient. -/
def AdmitsExtensionGroup (S : G → MulAut N) (omega : G → G → N) : Prop :=
  ∃ grp : Group (N × G), grp.mul = extensionProduct S omega

/-- Sanity: the ordinary product group witnesses the trivial factor system. -/
example : AdmitsExtensionGroup (fun (_ : G) => MulEquiv.refl N)
    (fun _ _ => (1 : N)) := by
  refine ⟨inferInstance, ?_⟩
  funext a b
  change (a.1 * b.1, a.2 * b.2) = (a.1 * b.1 * 1, a.2 * b.2)
  simp only [mul_one]

end QAlgorithms.Papers.Independent.Renew46.P27


