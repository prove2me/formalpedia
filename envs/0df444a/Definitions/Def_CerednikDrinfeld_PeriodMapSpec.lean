-- Prove2me | Definitions.Def_CerednikDrinfeld_PeriodMapSpec
-- name    : CerednikDrinfeld_PeriodMapSpec
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/67067e66-5b70-536f-ae04-60d57ea8998c
-- title:
--   Specification of a period map to the formal upper half plane
-- statement:
--   The standing data are a prime $p$, an algebraically closed field $k$ of characteristic $p$, and a ring homomorphism $\iota\colon\mathbb Z_{p^2}\to W(k)$. Relative to these, `IsPeriodMap` is a predicate on a family of maps $\theta$, formulated against: a `FormalODModule` $\Phi$ over $W(k)/pW(k)$; a `ModuliPackage` $M$, which assigns a set `M.obj B ψ hB` to every commutative ring $B$ with a ring homomorphism $\psi\colon W(k)\to B$ in which $p$ is nilpotent, together with transition maps `M.map` along ring homomorphisms commuting with the $\psi$'s; a family $\eta$ sending, for each such $(B,\psi)$, an element of `Rigidified p Φ B` to an element of `M.obj B ψ hB`; the hypothesis `hcΦ` that the graded pieces of degrees $0$ and $1$ of the Cartier module of $\Phi$ are complementary, the piece of degree $n$ consisting of those $f$ on which the action of the Teichmüller lift of $c\in\mathbb F_{p^2}$ agrees with the homothety by $j(\tau(c))^{p^n}$, where $j$ is $\iota$ followed by reduction mod $p$; and an additive map $r_\Phi$ from $\mathbb Z_p^{2}$ into the `NMod` of the graded Cartier module data attached to $\Phi$ by $j$ and `hcΦ`. Finally $\theta$ assigns, to each Noetherian $\mathbb Z_p$-algebra $B$ with $\psi\colon W(k)\to B$ and $p$ nilpotent, a map from `M.obj B ψ hB` to the Deligne data over $B$ for $\mathcal O=\mathbb Z_p$, $K=\mathbb Q_p$, $\pi=p$: families of $B$-submodules $\mathcal L(N)\subseteq B\otimes_{\mathbb Z_p}N$, indexed by the full $\mathbb Z_p$-lattices $N\subset\mathbb Q_p^2$, with invertible quotients, monotone under inclusions of lattices, equivariant for scalar homotheties, and nondegenerate at every prime of $B$.
--
--   The predicate is the conjunction of two conditions. First, compatibility with Cartier theory: for every such $B$, every $t$ in `Rigidified p Φ B` satisfying `IsAdmissible ι ψ`, and every `DrinfeldDatum` $Q$ over $B$ which is a Cartier quadruple of $t$ with respect to $\iota$, `hcΦ`, $r_\Phi$ and $\psi$, one has that $Q$ is a Drinfeld quadruple of the Deligne datum $\theta_B(\eta_B(t))$ — at every prime $x$ of $B$ the pair of lattices $N_0(x)\subseteq N_1(x)$ is edge‑nondegenerate for that datum, and the kernels of $u_0(x)$ and $u_1(x)$ are exactly its lines at those two lattices after base change to the local ring at $x$. Second, compatibility with base change: for $\mathbb Z_p$-algebra homomorphisms $f\colon B\to B'$ between Noetherian $\mathbb Z_p$-algebras with $p$ nilpotent and $\psi'=f\circ\psi$, the Deligne datum attached by $\theta$ to the image of $x$ under `M.map` is the base change along $f$ of $\theta_B(x)$, i.e. each of its lines is the $B'$-span of the image of the corresponding line.
--
--   **Relation to Mathlib.** Mathlib has no formal upper half plane, Deligne or Drinfeld data, or graded Cartier modules; `IsPeriodMap` is stated entirely in the project's own vocabulary, using from Mathlib only Witt vectors, $p$-adic rings, localisations and submodule/tensor constructions.
--
--   **Where it is used.** The predicate is the specification with which the local statements about Drinfeld's $p$-adic uniformisation functor are organised: the existence of such a $\theta$, its equivariance, and its bijectivity on points are each formulated as assertions about a family satisfying `IsPeriodMap`. The resulting Čerednik–Drinfeld description of Shimura curves at $p$ feeds the quaternionic side of the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_PeriodMapSpec.lean

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

namespace CerednikDrinfeld.SpecialFormal.ModuliPackage

def IsPeriodMap
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
  (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
      (hB : IsNilpotent (p : B)) (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
      ∀ Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B, t.IsCartierQuadruple ι hcΦ rΦ ψ Q →
        Q.IsQuadrupleOf (θ B ψ hB (η B ψ hB t))) ∧
  (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
    (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →ₐ[ℤ_[p]] B')
    (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
    DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) f (θ B ψ hB x)
      (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x)))

end CerednikDrinfeld.SpecialFormal.ModuliPackage


