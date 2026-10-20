-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation__EvenBarker
-- name    : OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation__EvenBarker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:48:37.231794+00:00
-- url     : https://prove2.me/theorems/85af86d3-8915-4c53-bfe6-5308668c1260
-- title:
--   Evaluating the cyclic group ring at a character
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction. Write $R[\mathbb Z/n]$ for the cyclic group ring (finitely supported coefficient functions on $\mathbb Z/n$ with convolution), $e_a$ for its basis element at $a$, and $f^{*}(a)=\overline{f(-a)}$ for its involution, which reverses indices and applies the coefficient star.
--
--   1. **Character evaluation.** For a ring homomorphism $\varphi:R\to S$ into a commutative ring and a character $\chi$ of $\mathbb Z/n$ with values in $S$ (a multiplicative homomorphism), the ring homomorphism
--   $$
--   \mathrm{ev}_{\varphi,\chi}(f)=\sum_{a\in\mathbb Z/n}\varphi\bigl(f(a)\bigr)\,\chi(a).
--   $$
--   It sends the scalar $r$ to $\varphi(r)$, and at the trivial character it is $\varphi$ composed with augmentation.
--   2. **Compatibility with the involution.** If $\varphi(\bar r)=\overline{\varphi(r)}$ and $\chi(-a)=\overline{\chi(a)}$, then $\mathrm{ev}(f^{*})=\overline{\mathrm{ev}(f)}$. Hence a norm equation $ff^{*}=r$ in the group ring gives $\mathrm{ev}(f)\,\overline{\mathrm{ev}(f)}=\varphi(r)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/CyclicEvaluation.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/CyclicEvaluation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EvenBarker mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_PeriodicModFour
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal__EvenBarker

namespace OAI

universe uR uS uT uA

/-!
# Evaluation of the finite cyclic group ring

Evaluation is a ring homomorphism obtained from a coefficient homomorphism and
an actual character of the cyclic group.  Its compatibility with the group-ring
involution is proved from the coefficient and character identities.
-/

noncomputable section

namespace CirculantHadamard.CyclicRing

open scoped BigOperators

variable {R : Type uR} {S : Type uS} {T : Type uT} [Semiring R] [CommSemiring S] [CommSemiring T]
variable {n : ℕ}

/-- Evaluation at a multiplicative character of the additive cyclic group. -/
def evaluate (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S) : Elem R n →+* S :=
  AddMonoidAlgebra.liftNCRingHom φ χ (fun _ _ => Commute.all _ _)

@[simp] theorem evaluate_single (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (a : ZMod n) (r : R) :
    evaluate φ χ (AddMonoidAlgebra.single a r) = φ r * χ (Multiplicative.ofAdd a) :=
  AddMonoidAlgebra.liftNC_single _ _ _ _

@[simp] theorem evaluate_scalar (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (r : R) :
    evaluate φ χ (scalar n r) = φ r := by
  simp only [scalar, evaluate_single]
  change φ r * χ 1 = φ r
  simp

/-- The full finite sum, rather than a sum over an unspecified support. -/
theorem evaluate_apply [NeZero n] (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (f : Elem R n) :
    evaluate φ χ f = ∑ a : ZMod n, φ (f.coeff a) * χ (Multiplicative.ofAdd a) := by
  change f.coeff.sum (fun a r => φ r * χ (Multiplicative.ofAdd a)) = _
  exact Finsupp.sum_fintype f.coeff _ (fun _ => by simp)

@[simp] theorem evaluate_ofCoeffs [NeZero n] (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (c : ZMod n → R) :
    evaluate φ χ (ofCoeffs c) = ∑ a : ZMod n, φ (c a) * χ (Multiplicative.ofAdd a) :=
  evaluate_apply φ χ (ofCoeffs c)

/-- The trivial character recovers augmentation followed by the coefficient map. -/
theorem evaluate_trivial_eq_augmentation [NeZero n] (φ : R →+* S)
    (f : Elem R n) :
    evaluate φ (1 : Multiplicative (ZMod n) →* S) f = φ (augmentation n f) := by
  simp [evaluate_apply, augmentation_apply, map_sum]

/-- A target endomorphism intertwines evaluation and the full group-ring star
when it intertwines the coefficient involution and character inversion. -/
theorem evaluate_ringStar_intertwining [StarRing R] [NeZero n]
    (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S) (τ : S →+* S)
    (hφ : ∀ r, φ (star r) = τ (φ r))
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = τ (χ (Multiplicative.ofAdd a)))
    (f : Elem R n) :
    evaluate φ χ (ringStar f) = τ (evaluate φ χ f) := by
  rw [evaluate_apply, evaluate_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ ?_
  intro a
  simp only [ringStar_apply, Equiv.neg_apply, map_mul, hφ]
  rw [← hχ]
  simp only [neg_neg]

/-- Character evaluation carries the full group-ring involution to target star. -/
theorem evaluate_ringStar [StarRing R] [StarRing S] [NeZero n]
    (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = star (χ (Multiplicative.ofAdd a)))
    (f : Elem R n) :
    evaluate φ χ (ringStar f) = star (evaluate φ χ f) :=
  evaluate_ringStar_intertwining φ χ (starRingEnd S) hφ hχ f

/-- The group-ring norm product becomes the usual star norm product. -/
theorem evaluate_mul_ringStar [StarRing R] [StarRing S] [NeZero n]
    (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = star (χ (Multiplicative.ofAdd a)))
    (f : Elem R n) :
    evaluate φ χ (f * ringStar f) = evaluate φ χ f * star (evaluate φ χ f) := by
  rw [map_mul, evaluate_ringStar φ χ hφ hχ]

/-- A proved scalar group-ring norm equation transfers to every compatible
character; the norm equation is not built into the evaluation definition. -/
theorem evaluate_norm_eq [StarRing R] [StarRing S] [NeZero n]
    (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = star (χ (Multiplicative.ofAdd a)))
    (f : Elem R n) (r : R) (hf : f * ringStar f = scalar n r) :
    evaluate φ χ f * star (evaluate φ χ f) = φ r := by
  rw [← evaluate_mul_ringStar φ χ hφ hχ, hf, evaluate_scalar]

end CirculantHadamard.CyclicRing

end

end OAI


