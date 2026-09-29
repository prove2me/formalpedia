-- Prove2me | Definitions.Def_ModularCurve_DegeneracyVp
-- name    : ModularCurve_DegeneracyVp
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/2f01e48c-10b8-5fb7-8a79-1a0c3a28c632
-- title:
--   p-adic degeneracy maps and old/new parts of the Jacobian
-- statement:
--   Fix natural numbers $N,q\ge 1$ and a prime $p$. The module first records the functoriality of the Tate module in the abelian group: for additive groups $J,J'$ and $f\colon J\to J'$, `tateMap` sends a sequence in $J$ satisfying the torsion and compatibility conditions defining [`TateModule p J`](../def/EllipticCurve_TateModule.html#L15) to the termwise image sequence in $J'$ (the conditions are preserved because they are equalities between integer multiples), `tateMap_apply` is its evaluation rule, `tateMapLin` is the same map viewed as $\mathbb{Z}_p$-linear, and `vpMap` is its base change to a $\mathbb{Q}_p$-linear map $V_p(J)\to V_p(J')$ between the rational Tate modules. Applying `vpMap` to the two degeneracy pushforwards $J_0(Nq)\to J_0(N)$ of the toric descent data gives `vpDegeneracyPush N q p i` for $i\in\{0,1\}$, and `newPartVp` is defined as the intersection of their kernels. In the other direction, `DegeneracyPullbackInputs` asserts the existence of integrality for the two degeneracy embeddings $\bar\alpha$ (inclusion of the level-$N$ Laurent-series function field into the level-$Nq$ one) and $\bar\beta$ (induced by $q$-expansion rescaling), of the principal-divisor hypothesis at level $Nq$, and of the fundamental identity along each of $\bar\alpha,\bar\beta$; under it `degeneracyPullbackPair` is the pair of pullback homomorphisms $J_0(N)\to J_0(Nq)$ on degree-zero divisor classes, and is $0$ otherwise. Similarly `HeckeTransposeInputsAlong` collects integrality of both legs, principal divisors at level $Nq$, finiteness along $\bar\beta$, the fundamental identity along $\bar\alpha$ and the norm formula along $\bar\beta$, and `heckeOperatorTransposeAlong` is the corresponding transposed correspondence $\bar\alpha^{*}$ followed by $\bar\beta_{*}$ on $J_0(N)$, zero when the inputs fail. The $\mathbb{Q}_p$-linear realisations `vpDegeneracyPull`, the joint maps `vpJointPush` (product of the two pushforwards) and `vpJointPull` (coproduct of the two pullbacks), the old part `oldPartVp` as the range of `vpJointPull`, and the Gram endomorphism `oldNewGramVp` of $V_p(J_0(N))^2$ given by `vpJointPull` followed by `vpJointPush`, complete the vocabulary. Two lemmas identify `newPartVp` with the kernel of `vpJointPush` and `oldPartVp` with the sum of the ranges of the two pullbacks. Nothing is asserted here about invertibility of the Gram endomorphism or about an old/new splitting.
--
--   **Relation to Mathlib.** The linear-algebra scaffolding (`LinearMap.baseChange`, `LinearMap.prod`, `LinearMap.coprod` and the identities `LinearMap.ker_prod`, `LinearMap.range_coprod`) is Mathlib's; the levelwise Tate module of an abelian group, the Jacobian `JZero`, the degeneracy maps and the old/new submodules are the project's own notions.
--
--   **Where it is used.** This is the $p$-adic vocabulary in which the $q$-old and $q$-new parts of $V_p(J_0(Nq))$, and the degeneracy and transposed Hecke maps relating levels $N$ and $Nq$, are stated; it underlies the level-lowering step of the route to Fermat's Last Theorem, where a mod $p$ representation occurring at level $Nq$ is shown to occur at level $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_DegeneracyVp.lean

import Definitions.Def_ModularCurve_HeckeSeam
import Definitions.Def_ModularCurve_ToricDescentData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

section Functorial

variable (p : ℕ) [Fact p.Prime] {J J' : Type} [AddCommGroup J] [AddCommGroup J']

def tateMap (f : J →+ J') : TateModule p J →+ TateModule p J' where
  toFun x := ⟨fun n => f ((x : ℕ → J) n), fun n =>
    ⟨by rw [← map_zsmul f, TateModule.torsion x n, map_zero],
     by rw [← map_zsmul f, TateModule.compat x n]⟩⟩
  map_zero' := Subtype.ext (funext fun n => by
    show f (((0 : TateModule p J) : ℕ → J) n) = ((0 : TateModule p J') : ℕ → J') n
    rw [TateModule.coe_zero, Pi.zero_apply, map_zero, TateModule.coe_zero, Pi.zero_apply])
  map_add' x y := Subtype.ext (funext fun n => by
    show f (((x + y : TateModule p J) : ℕ → J) n) = _
    rw [TateModule.coe_add, Pi.add_apply, map_add]
    rfl)

omit [Fact (Nat.Prime p)] in
@[simp] theorem tateMap_apply (f : J →+ J') (x : TateModule p J) (n : ℕ) :
    ((tateMap p f x : TateModule p J') : ℕ → J') n = f ((x : ℕ → J) n) :=
  rfl

def tateMapLin (f : J →+ J') : TateModule p J →ₗ[ℤ_[p]] TateModule p J' where
  toFun := tateMap p f
  map_add' := (tateMap p f).map_add
  map_smul' a x := Subtype.ext (funext fun n => by
    rw [RingHom.id_apply]
    show ((tateMap p f (a • x) : TateModule p J') : ℕ → J') n =
      ((a • tateMap p f x : TateModule p J') : ℕ → J') n
    rw [tateMap_apply, TateModule.smul_apply, TateModule.smul_apply, map_zsmul, tateMap_apply])

def vpMap (f : J →+ J') :
    RationalTateModule p J →ₗ[ℚ_[p]] RationalTateModule p J' :=
  LinearMap.baseChange ℚ_[p] (tateMapLin p f)

end Functorial

section OldNew

variable (N q : ℕ) [NeZero N] [NeZero q] (p : ℕ) [Fact p.Prime]

def vpDegeneracyPush (i : Fin 2) :
    RationalTateModule p (JZero (N * q)) →ₗ[ℚ_[p]] RationalTateModule p (JZero N) :=
  vpMap p (degeneracyPushforwardPair N q i)

def newPartVp : Submodule ℚ_[p] (RationalTateModule p (JZero (N * q))) :=
  LinearMap.ker (vpDegeneracyPush N q p 0) ⊓ LinearMap.ker (vpDegeneracyPush N q p 1)

end OldNew

section OldNewPull

variable (N q : ℕ) [NeZero N] [NeZero q] (p : ℕ) [Fact p.Prime]

def DegeneracyPullbackInputs : Prop :=
  ∃ (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (_ : HasPrincipalDivisors (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))),
    FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα ∧
      FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ

open Classical in

def degeneracyPullbackPair : Fin 2 → (JZero N →+ JZero (N * q)) :=
  if h : DegeneracyPullbackInputs N q then
    ![letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
      haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) N q)
      haveI := isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) N q) h.fst
      haveI := h.snd.snd.fst
      haveI : FundamentalIdentity (AlgebraicClosure ℚ)
          ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q))) :=
        h.snd.snd.snd.1
      Pic0.pullbackHom _,
      letI := algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) N q)
      haveI := isScalarTower_along (heckeBetaBar (AlgebraicClosure ℚ) N q)
      haveI := isIntegral_along (heckeBetaBar (AlgebraicClosure ℚ) N q) h.snd.fst
      haveI := h.snd.snd.fst
      haveI : FundamentalIdentity (AlgebraicClosure ℚ)
          ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q))) :=
        h.snd.snd.snd.2
      Pic0.pullbackHom _]
  else 0

def HeckeTransposeInputsAlong : Prop :=
  ∃ (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (_ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (_ : HasPrincipalDivisors (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q))))
    (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q)),
    FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα ∧
      NormFormulaAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) hfin

open Classical in

def heckeOperatorTransposeAlong : JZero N →+ JZero N :=
  if h : HeckeTransposeInputsAlong N q then
    haveI := h.snd.snd.fst
    heckePic0BarTranspose h.fst h.snd.fst h.snd.snd.snd.snd.1 h.snd.snd.snd.fst
      h.snd.snd.snd.snd.2
  else 0

def vpDegeneracyPull (i : Fin 2) :
    RationalTateModule p (JZero N) →ₗ[ℚ_[p]] RationalTateModule p (JZero (N * q)) :=
  vpMap p (degeneracyPullbackPair N q i)

def vpJointPush :
    RationalTateModule p (JZero (N * q)) →ₗ[ℚ_[p]]
      RationalTateModule p (JZero N) × RationalTateModule p (JZero N) :=
  LinearMap.prod (vpDegeneracyPush N q p 0) (vpDegeneracyPush N q p 1)

def vpJointPull :
    RationalTateModule p (JZero N) × RationalTateModule p (JZero N) →ₗ[ℚ_[p]]
      RationalTateModule p (JZero (N * q)) :=
  LinearMap.coprod (vpDegeneracyPull N q p 0) (vpDegeneracyPull N q p 1)

def oldPartVp : Submodule ℚ_[p] (RationalTateModule p (JZero (N * q))) :=
  LinearMap.range (vpJointPull N q p)

def oldNewGramVp :
    Module.End ℚ_[p]
      (RationalTateModule p (JZero N) × RationalTateModule p (JZero N)) :=
  (vpJointPush N q p).comp (vpJointPull N q p)

theorem ker_vpJointPush : LinearMap.ker (vpJointPush N q p) = newPartVp N q p :=
  LinearMap.ker_prod _ _

theorem oldPartVp_eq_sup :
    oldPartVp N q p =
      LinearMap.range (vpDegeneracyPull N q p 0) ⊔ LinearMap.range (vpDegeneracyPull N q p 1) :=
  LinearMap.range_coprod _ _

end OldNewPull

end ModularCurve

end


