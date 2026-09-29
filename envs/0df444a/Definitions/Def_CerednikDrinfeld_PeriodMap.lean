-- Prove2me | Definitions.Def_CerednikDrinfeld_PeriodMap
-- name    : CerednikDrinfeld_PeriodMap
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/ebffbf42-6731-594b-bc0f-48e10f66c52f
-- title:
--   Period values and period maps for rigidified special formal modules
-- statement:
--   Throughout, $p$ is a prime, $O$ a commutative ring, $\Phi$ a `FormalODModule` over $O/pO$, and $B$ a commutative ring. Fixed once and for all are a ring homomorphism $\iota\colon \mathbb{Z}_{p^2}\to O$, a proof `hc\Phi` that the two graded pieces `\Phi.gradedPiece (jbar \iota) 0` and `... 1` are complementary submodules, and an additive map $r_\Phi$ from $\mathbb{Z}_p^{\,2}$ into the `NMod` of the graded Cartier module data attached to $\Phi$ along the reduction of $\iota$ (that data being a Witt-vector module with Frobenius, Verschiebung, a square root $\varpi$ of $p$ and a $\mathbb{Z}/2$-grading). Given $\psi\colon O\to B$ and a rigidified object $t$ of `Rigidified p \Phi B`, the predicate `IsPeriodValue` on a point $d$ of $\hat\Omega(B)$ — that is, on a Deligne datum for $K=\mathbb{Q}_p$, $\pi=p$, consisting of a line bundle-quotient datum $M\mapsto \mathrm{line}(M)\subseteq B\otimes_{\mathbb{Z}_p}M$ on full lattices, monotone, homothety-equivariant and nondegenerate at every prime of $B$ — asserts the existence of a Drinfeld datum $Q$ over $B$ (lattice chains $N_0\subseteq N_1$ over $\operatorname{Spec}B$ together with invertible modules $T_0,T_1$, maps $\Pi_0,\Pi_1$ with both composites multiplication by $p$, and surjections $u_0,u_1$ onto the stalks) such that the predicate `IsCartierQuadruple` holds for $t$ and $Q$ relative to $(\iota,h_{c\Phi},r_\Phi,\psi)$ and such that $Q$ `IsQuadrupleOf` $d$, i.e. at every prime $x$ the datum $d$ is edge-nondegenerate for $(N_0(x),N_1(x))$ and the kernels of $u_0(x),u_1(x)$ are the lines of the localised $d$ at those two lattices. `periodValue` extracts such a $d$ from a proof of its existence, and `periodValue_spec` records that the extracted value satisfies `IsPeriodValue`.
--
--   Finally, `IsPeriodMapOn` fixes $k$ algebraically closed of characteristic $p$, $\iota\colon\mathbb{Z}_{p^2}\to W(k)$, $\Phi$ over $W(k)/p$, a moduli package $M$ with a comparison family $\eta$ from rigidified objects to $M$, and a candidate period map $\theta$ defined on $M.\mathrm{obj}\,B\,\psi$ for Noetherian $\mathbb{Z}_p$-algebras $B$ with $p$ nilpotent; it asserts that for every such $B$, every $\psi\colon W(k)\to B$ and every admissible $t$, the Deligne datum $\theta(\eta(t))$ is a period value of $t$. This is the existential form of the condition; the predicate `IsPeriodMap` of the imported specification instead requires that every Cartier quadruple of $t$ be a quadruple of $\theta(\eta(t))$ and adds compatibility of $\theta$ with base change along $\mathbb{Z}_p$-algebra maps.
--
--   **Relation to Mathlib.** Mathlib has no notion of Deligne or Drinfeld data, of special formal $\mathcal{O}_D$-modules or of their Cartier modules; these are the project's own structures, built on Mathlib's Witt vectors, $p$-adic integers, submodules and localised modules.
--
--   **Where it is used.** These predicates axiomatise the period morphism from the moduli of rigidified special formal modules over $W(k)$ to Drinfeld's formal upper half plane, the analytic input to the Čerednik–Drinfeld uniformisation of Shimura curves at a prime of bad reduction. That uniformisation underlies the study of the reduction and component groups of the modular and Shimura curves used in the level-lowering step of the route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_PeriodMap.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace CerednikDrinfeld.SpecialFormal.Rigidified

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]
variable {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [CommRing B]

def IsPeriodValue (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (d : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B) : Prop :=
  ∃ Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B, t.IsCartierQuadruple ι hcΦ rΦ ψ Q ∧ Q.IsQuadrupleOf d

noncomputable def periodValue (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (h : ∃ d : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B, t.IsPeriodValue ι hcΦ rΦ ψ d) :
    OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B :=
  h.choose

theorem periodValue_spec (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (h : ∃ d : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B, t.IsPeriodValue ι hcΦ rΦ ψ d) :
    t.IsPeriodValue ι hcΦ rΦ ψ (t.periodValue ι hcΦ rΦ ψ h) :=
  h.choose_spec

end CerednikDrinfeld.SpecialFormal.Rigidified

namespace CerednikDrinfeld.SpecialFormal.ModuliPackage

def IsPeriodMapOn
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(M : ModuliPackage.{0, 0} p (WittVector p k))
(η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
Rigidified p Φ B → M.obj B ψ hB)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
M.obj B ψ hB → OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B) : Prop :=
  ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B)) (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
    t.IsPeriodValue ι hcΦ rΦ ψ (θ B ψ hB (η B ψ hB t))

end CerednikDrinfeld.SpecialFormal.ModuliPackage


