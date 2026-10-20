-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection__EvenBarker
-- name    : OAI_LinearAlgebra_CirculantHadamard_CyclicProjection__EvenBarker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:43:08.482176+00:00
-- url     : https://prove2.me/theorems/8612bab4-fdab-4e03-88a1-eb9eadf33736
-- title:
--   Projection of cyclic group rings by reducing indices
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction. Write $R[\mathbb Z/n]$ for the cyclic group ring (finitely supported coefficient functions on $\mathbb Z/n$ with convolution), $e_a$ for its basis element at $a$, and $f^{*}(a)=\overline{f(-a)}$ for its involution, which reverses indices and applies the coefficient star.
--
--   1. **Cyclic projection.** For $m\mid n$, the ring homomorphism $\pi_{n\to m}:R[\mathbb Z/n]\to R[\mathbb Z/m]$ induced by reduction $\mathbb Z/n\to\mathbb Z/m$, that is
--   $$
--   \pi_{n\to m}\Bigl(\sum_af(a)\,e_a\Bigr)=\sum_af(a)\,e_{a\bmod m}.
--   $$
--   It sends the generator $e_1$ to $e_1$, fixes scalars, is the identity when $m=n$, preserves augmentation, and commutes with the involution $f\mapsto f^{*}$. The coefficient of $\pi_{n\to m}(f)$ at $b$ is the sum of $f$ over the fibre of $b$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/CyclicProjection.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/CyclicProjection.lean by skeleton subtraction
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

namespace OAI

universe uR uS

/-!
# Quotients of actual cyclic group rings

For `m ∣ n`, reduction of indices defines the quotient map from the cyclic
group ring of order `n` to that of order `m`. In particular it sends the
distinguished generator to the distinguished generator and fixes scalars.
The definition is the convolution ring homomorphism induced by `ZMod.castHom`.
-/

noncomputable section

namespace CirculantHadamard

open CyclicRing

variable (R : Type uR) [Semiring R] {m n l : ℕ}

/-- The quotient of cyclic group rings induced by reduction of indices. -/
def cyclicProjection (h : m ∣ n) : Elem R n →+* Elem R m :=
  AddMonoidAlgebra.mapDomainRingHom R (ZMod.castHom h (ZMod m)).toAddMonoidHom

variable {R}

@[simp] theorem cyclicProjection_single (h : m ∣ n) (a : ZMod n) (r : R) :
    cyclicProjection R h (AddMonoidAlgebra.single a r) =
      AddMonoidAlgebra.single (ZMod.castHom h (ZMod m) a) r :=
  AddMonoidAlgebra.mapDomain_single

@[simp] theorem cyclicProjection_single_zero (h : m ∣ n) (r : R) :
    cyclicProjection R h (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 r := by
  simp

@[simp] theorem cyclicProjection_scalar (h : m ∣ n) (r : R) :
    cyclicProjection R h (scalar n r) = scalar m r := by
  exact cyclicProjection_single_zero h r

@[simp] theorem cyclicProjection_generator (h : m ∣ n) :
    cyclicProjection R h (AddMonoidAlgebra.single 1 1) = AddMonoidAlgebra.single 1 1 := by
  simp only [cyclicProjection_single, map_one]

@[simp] theorem cyclicProjection_single_natCast (h : m ∣ n) (a : ℕ) (r : R) :
    cyclicProjection R h (AddMonoidAlgebra.single (a : ZMod n) r) =
      AddMonoidAlgebra.single (a : ZMod m) r := by
  simp

@[simp] theorem cyclicProjection_self (F : Elem R n) :
    cyclicProjection R (dvd_refl n) F = F := by
  apply AddMonoidAlgebra.coeff_injective
  change Finsupp.mapDomain (ZMod.castHom (dvd_refl n) (ZMod n)) F.coeff = F.coeff
  simp [ZMod.castHom_self]

/-- Any additive coefficient evaluation factors through the quotient exactly
when its index function is pulled back along reduction. -/
theorem sum_cyclicProjection {S : Type uS} [AddCommMonoid S]
    (h : m ∣ n) (F : Elem R n) (v : ZMod m → R →+ S) :
    (cyclicProjection R h F).coeff.sum (fun a r => v a r) =
      F.coeff.sum (fun a r => v (ZMod.castHom h (ZMod m) a) r) :=
  Finsupp.sum_mapDomain_index_addMonoidHom v

/-- Evaluation at the trivial character is unchanged by the cyclic quotient. -/
@[simp] theorem augmentation_cyclicProjection (h : m ∣ n) (F : Elem R n) :
    augmentation m (cyclicProjection R h F) = augmentation n F := by
  change (cyclicProjection R h F).coeff.sum (fun _ r => r * 1) =
    F.coeff.sum (fun _ r => r * 1)
  simp only [mul_one]
  exact sum_cyclicProjection h F (fun _ => AddMonoidHom.id R)

section Star

variable [StarRing R] [NeZero m] [NeZero n]

/-- Quotienting the indices commutes with conjugation and index reversal. -/
@[simp] theorem cyclicProjection_ringStar (h : m ∣ n) (F : Elem R n) :
    cyclicProjection R h (ringStar F) = ringStar (cyclicProjection R h F) := by
  refine AddMonoidAlgebra.induction_linear F ?_ ?_ ?_
  · simp
  · intro F G hF hG
    change cyclicProjection R h (ringStar ((F : Elem R n) + G)) =
      ringStar (cyclicProjection R h ((F : Elem R n) + G))
    calc
      _ = cyclicProjection R h (ringStar F + ringStar G) :=
        congrArg (cyclicProjection R h) (ringStar_add F G)
      _ = cyclicProjection R h (ringStar F) + cyclicProjection R h (ringStar G) :=
        (cyclicProjection R h).map_add _ _
      _ = ringStar (cyclicProjection R h F) + ringStar (cyclicProjection R h G) :=
        congrArg₂ (· + ·) hF hG
      _ = ringStar (cyclicProjection R h F + cyclicProjection R h G) :=
        (ringStar_add _ _).symm
      _ = _ := congrArg ringStar ((cyclicProjection R h).map_add F G).symm
  · intro a r
    simp only [ringStar_single, cyclicProjection_single, map_neg]

end Star

end CirculantHadamard

end

end OAI


