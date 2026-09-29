-- Prove2me | Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia
-- name    : CerednikDrinfeld_CartierQuadrupleVia
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/abaa5b6f-bdff-509e-9fc5-ac9153521430
-- title:
--   Cartier quadruple relation with prescribed tangent identifications
-- statement:
--   Throughout, $p$ is a prime, $O$ a commutative ring, $\Phi$ a formal $O_D$-module over $O/pO$ (the quotient by `pIdeal p O`), and $B$ a commutative $\mathbb{Z}_p$-algebra. The predicate `IsCartierQuadrupleVia` takes: a ring homomorphism $\iota$ from `Zp2 p` (Witt vectors over $\mathbb{F}_{p^2}$) to $O$; a witness `hcΦ` that the two graded pieces $\Phi.\mathrm{gradedPiece}(\overline{\iota},0)$ and $\Phi.\mathrm{gradedPiece}(\overline{\iota},1)$ of the Cartier module of $\Phi$ — the subgroups on which the Teichmüller action of $\mathbb{F}_{p^2}$ agrees with homothety by the $p^n$-th power of its image — are complementary; an additive map $r_\Phi$ from $\mathbb{Z}_p^{2}$ to the `NMod` of the graded Cartier module data attached to $\Phi$ and `hcΦ`; a ring homomorphism $\psi : O \to B$; a rigidified object $t$ of `Rigidified p Φ B`, with formal module $t.X$, reduction $t.\mathrm{Xbar}$ and rigidification $t.\rho$; a Drinfeld datum $Q$ over $B$ for $\mathcal{O}=\mathbb{Z}_p$, $K=\mathbb{Q}_p$, $\pi=p$ (lattices $N_0(x)\subseteq N_1(x)$ in $\mathbb{Q}_p^2$ indexed by $x\in\operatorname{Spec}B$, invertible $B$-modules $T_0,T_1$ with $\Pi_0,\Pi_1$ composing to multiplication by $p$, and surjections $u_i$ onto the stalks); and $B$-linear isomorphisms $\tau_0 : T_0 \cong t.X.\mathrm{lieZero}$, $\tau_1 : T_1 \cong t.X.\mathrm{lieOne}$ of $T_i$ with the graded pieces of the Lie algebra of $t.X$ for the structure map determined by $\iota$ and $\psi$. The asserted conjunction is: $t.\rho$ is an $O_D$-homomorphism from $t.\Phi\mathrm{bar}\,\psi$ to $t.\mathrm{Xbar}$; $\tau_1\circ\Pi_0$ and $\tau_0\circ\Pi_1$ both agree with the action `lieVarpi` of the uniformiser on the Lie algebra, composed with $\tau_0$ resp. $\tau_1$; and, for every witness of that $O_D$-linearity (it enters the $\eta$-sections) and every prime $x$ of $B$, four clauses. The first two characterise membership $v\in N_n(x)$ for $n=0,1$ as the existence of $f\notin x$ together with the graded compatibilities `IsGradedS`, `IsGradedSbar`, `IsGradedPhiS` for the localisation of $B$ away from $f$, a map $L$ satisfying `IsCanonicalLMap` for the graded Cartier module data of $t.\mathrm{XS}$ over that localisation, and an element $z$ with `IsEtaSection … n z v`. The last two say that for any such $v\in N_n(x)$ and any such choice of $f$, $L$ and $z$ there are $m$ in the module $M$ of that graded Cartier module data, $s\in T_n$ and $b\notin x$ with: the class of $m$ modulo the image of Verschiebung equal to the image of $z$ under the map `u` determined by $L$; $u_n(x)(1\otimes v) = s/b$ in the stalk of $T_n$ at $x$; and, coordinatewise, the image of $\tau_n(s)$ in the local ring at $x$ equal to $b$ times the image of the tangent vector of $m$. The theorem `isCartierQuadruple_iff_exists_via` states that `t.IsCartierQuadruple ι hcΦ rΦ ψ Q` holds if and only if $t.\rho$ is an $O_D$-homomorphism and such $\tau_0,\tau_1$ exist with `IsCartierQuadrupleVia`; the two sides differ only by moving the existential quantifiers over $\tau_0,\tau_1$ and by repeating the $O_D$-linearity clause, so the equivalence is a matter of unfolding the definitions.
--
--   **Relation to Mathlib.** Formal $O_D$-modules, graded Cartier module data and Drinfeld data are notions of this development with no counterpart in Mathlib; the statement is phrased using Mathlib's Witt vectors, `LocalizedModule` localisations and `PrimeSpectrum`.
--
--   **Where it is used.** The predicate is the body of the Cartier-quadruple relation with the tangent identifications named rather than hidden in an existential, which is what allows quadruples to be compared clause by clause (under base change, or along an isomorphism) in the project's treatment of the Čerednik–Drinfeld $p$-adic uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_CartierQuadrupleVia.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule

namespace CerednikDrinfeld.SpecialFormal.Rigidified

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]
variable {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [CommRing B]

def IsCartierQuadrupleVia (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (τ₀ : Q.T₀ ≃ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
    (τ₁ : Q.T₁ ≃ₗ[B] ↥(t.X.lieOne (structureMap ι ψ))) : Prop :=
  IsODHom (t.Φbar ψ) t.Xbar t.ρ ∧

    (∀ s : Q.T₀, ((τ₁ (Q.Pi₀ s) : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) =
        t.X.lieVarpi ((τ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie)) ∧
    (∀ s : Q.T₁, ((τ₀ (Q.Pi₁ s) : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) =
        t.X.lieVarpi ((τ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie)) ∧

    ∀ (hOD : IsODHom (t.Φbar ψ) t.Xbar t.ρ) (x : PrimeSpectrum B),

      (∀ v, v ∈ Q.N₀ x ↔
        ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (awayHom f))
          (hcb : t.IsGradedSbar ι ψ (awayHom f)) (hcΦf : IsGradedPhiS (Φ := Φ) ι ψ (awayHom f))
          (L : _) (hL : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
          ∃ z, t.IsEtaSection ι hcΦ rΦ ψ hOD (awayHom f) hc hcb hcΦf L hL 0 z v) ∧

      (∀ v, v ∈ Q.N₁ x ↔
        ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (awayHom f))
          (hcb : t.IsGradedSbar ι ψ (awayHom f)) (hcΦf : IsGradedPhiS (Φ := Φ) ι ψ (awayHom f))
          (L : _) (hL : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
          ∃ z, t.IsEtaSection ι hcΦ rΦ ψ hOD (awayHom f) hc hcb hcΦf L hL 1 z v) ∧

      (∀ (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₀ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (awayHom f)) (hcb : t.IsGradedSbar ι ψ (awayHom f))
          (hcΦf : IsGradedPhiS (Φ := Φ) ι ψ (awayHom f))
          (L : _) (hL : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ hOD (awayHom f) hc hcb hcΦf L hL 0 z v),
        ∃ (m : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).M) (s : Q.T₀)
          (b : x.asIdeal.primeCompl),
          ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          Q.u₀ x ((1 : Bloc x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₀ x))) = LocalizedModule.mk s b ∧
          ∀ i, locHom x ((τ₀ s : t.X.Lie) i) =
            locHom x (b : B) * awayToLoc x f hf (tangent m i)) ∧

      (∀ (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₁ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (awayHom f)) (hcb : t.IsGradedSbar ι ψ (awayHom f))
          (hcΦf : IsGradedPhiS (Φ := Φ) ι ψ (awayHom f))
          (L : _) (hL : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ hOD (awayHom f) hc hcb hcΦf L hL 1 z v),
        ∃ (m : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).M) (s : Q.T₁)
          (b : x.asIdeal.primeCompl),
          ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          Q.u₁ x ((1 : Bloc x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₁ x))) = LocalizedModule.mk s b ∧
          ∀ i, locHom x ((τ₁ s : t.X.Lie) i) =
            locHom x (b : B) * awayToLoc x f hf (tangent m i))

theorem isCartierQuadruple_iff_exists_via (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) :
    t.IsCartierQuadruple ι hcΦ rΦ ψ Q ↔
      IsODHom (t.Φbar ψ) t.Xbar t.ρ ∧
      ∃ (τ₀ : Q.T₀ ≃ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
        (τ₁ : Q.T₁ ≃ₗ[B] ↥(t.X.lieOne (structureMap ι ψ))), t.IsCartierQuadrupleVia ι hcΦ rΦ ψ Q τ₀ τ₁ := by
  constructor
  · rintro ⟨hOD, τ₀, τ₁, h⟩; exact ⟨hOD, τ₀, τ₁, hOD, h⟩
  · rintro ⟨hOD, τ₀, τ₁, -, h⟩; exact ⟨hOD, τ₀, τ₁, h⟩

end CerednikDrinfeld.SpecialFormal.Rigidified


