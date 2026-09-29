-- Prove2me | Definitions.Def_CerednikDrinfeld_FormalQuotientDatum
-- name    : CerednikDrinfeld_FormalQuotientDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/19fb41af-a08c-5ee7-b868-b44fa1233b81
-- title:
--   Formal quotient data for the Čerednik–Drinfeld uniformisation
-- statement:
--   Fix a commutative ring $\mathcal O$ with an element $\pi$, an $\mathcal O$-algebra field $K_0$, an $\mathcal O$-algebra $O^{nr}$ with an $\mathcal O$-algebra automorphism $\mathrm{Fr}$, a homomorphism $v\!\det : GL_2(K_0) \to \mathbb Z$ (written multiplicatively), a natural number $r$, a group $G$ with a homomorphism $\sigma : G \to GL_2(K_0)$, two subgroups $\Gamma, \Gamma' \le G$, and an element $g_1 \in GL_2(K_0)$. The structure `FormalQuotientDatum` is the data of a levelwise presentation by honest schemes of the formal quotient of the formal upper half-plane twisted by $O^{nr}$ under $\Gamma$, together with all of its characterising properties as further fields. Throughout, the $B$-points of the functor `AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)` are pairs $(\psi, P)$ consisting of an $\mathcal O$-algebra map $\psi : O^{nr} \to B$ and a point $P$ of the formal upper half-plane over $B$, i.e. a Deligne datum `DeligneDatum (K := K₀) π B`; the predicate `OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ)` relates two such pairs by the twisted action of $\gamma$.
--
--   The first group of fields gives schemes $Y_n$ with proper structure morphisms $Y_n \to \operatorname{Spec}(\mathcal O/\pi^{n+1})$ and transitions $Y_n \to Y_{n+1}$ whose squares over $\operatorname{Spec}(\mathcal O/\pi^{n+2}) \to \operatorname{Spec}(\mathcal O/\pi^{n+1})$ are cartesian. The second gives the quotient map: for every $\mathcal O$-algebra $B$ with $(\pi \cdot 1_B)^{n+1} = 0$ and every pair $(\psi,P)$ over $B$, a morphism $q_n(\psi,P) : \operatorname{Spec} B \to Y_n$ lying over $\operatorname{Spec}\mathcal O$ (field `q_over`), natural in $B$ (`q_natural`), compatible with the transitions (`q_yt`), and constant on twisted $\Gamma$-orbits (`q_inv`). The field `q_fib` asserts that for an algebraically closed field $k$ over $\mathcal O$ with $(\pi\cdot 1_k)^{n+1}=0$ and a fixed $\psi : O^{nr} \to k$, every $k$-point of $Y_n$ over $\mathcal O$ is $q_n(\psi,P)$ for some $P$, and $q_n(\psi,P) = q_n(\psi,P')$ exactly when $(\psi,P)$ and $(\psi,P')$ are related by the twisted action of some $\gamma \in \Gamma$. The field `univ` is the universal property, with its uniqueness clause: given a scheme $T$ over $\operatorname{Spec}\mathcal O$ and an assignment $\rho'$, for each $\mathcal O$-algebra $B$ with $\pi \cdot 1_B$ nilpotent, of $T$-valued points of $\operatorname{Spec}B$ over $\mathcal O$ (the functor `Scheme.nilpPoints`) that is natural in $B$ and invariant under the twisted $\Gamma$-action, there is a unique system of morphisms $u_n : Y_n \to T$ over $\operatorname{Spec}\mathcal O$, compatible with the transitions, with $q_n(x)$ followed by $u_n$ equal to $\rho'(x)$.
--
--   The remaining fields record the chartwise structure of the base change to $O^{nr}$. Schemes $Y^{nr}_n$ are presented as the fibre products $Y_n \times_{\operatorname{Spec}(\mathcal O/\pi^{n+1})} \operatorname{Spec}(O^{nr}/\pi^{n+1})$ with projections $p_1, p_2$ and transitions $j^{nr}_n$ compatible with both projections. For each $h \in GL_2(K_0)$ and each level there are an open $U(h,n) \subseteq Y^{nr}_n$, a ring homomorphism $c(h,n)$ from the sections over $U(h,n)$ to $A_n := \mathrm{chartERing}(O^{nr}, \pi, r)/\pi^{n+1}$ — the quotient of the localisation of $O^{nr}[\xi,\eta]/(\xi\eta - \pi)$ away from $(\xi^{r-1}-1)(\eta^{r-1}-1)$ — and a morphism $\kappa(h,n) : \operatorname{Spec}A_n \to Y^{nr}_n$; the fields `κ_preimage`, `c_const` and `U_jnr` say that $\kappa(h,n)$ factors through $U(h,n)$ and induces $c(h,n)$ on sections, that $c(h,n)$ is $O^{nr}/\pi^{n+1}$-linear in the sense of sending the pullbacks along $p_2$ of the classes of elements of $O^{nr}$ to their images in $A_n$, and that $U(h,n)$ is the preimage of $U(h,n+1)$ with $c$ compatible with the reductions $A_{n+1} \to A_n$. The field `cover` says the $U(h,n)$ cover $Y^{nr}_n$. The field `κ_p₁` identifies the chart: for $B$ an $O^{nr}$-algebra over $\mathcal O$ in a scalar tower, killed by $\pi^{n+1}$, an $O^{nr}$-algebra map $\bar x : A_n \to B$ and Deligne data $d, P$ over $B$ such that the line of $d$ at the standard lattice is spanned by $\bar x(\xi)\otimes e_0 + 1 \otimes e_1$, its line at $g_1 \cdot (\text{standard lattice})$ is the image of the span of $1 \otimes e_0 + \bar x(\eta)\otimes e_1$ under the base-changed action of $g_1$, and $d$ lies in the edge chart for the pair $(g_1 L_0, L_0)$ — meaning that for every prime ideal of $B$ the edge nondegeneracy conditions `DeligneDatum.EdgeNondegAt` hold — and such that $P$ is the $h^{-1}$-pullback of $d$, the composite of $\operatorname{Spec}\bar x$ with $\kappa(h,n)$ and $p_1(n)$ is $q_n$ of the pair consisting of the structure map $O^{nr} \to B$ and $P$. Finally `functions` describes the sections over a chart: compatible systems of sections on the $U(h,m)$ are determined by their images under the $c(h,m)$, and a compatible system $(\mathrm{fam}_m)$ of elements of the $A_m$ arises from such a system of sections precisely when it is invariant in the following sense: whenever two chart points $\bar x, \bar x' : A_m \to B$ carry edge-chart Deligne data $d, d'$ whose $h^{-1}$-pullbacks $P, P'$ are related by the pullback along $(\sigma\gamma)^{-1}$ for some $\gamma \in \Gamma'$, one has $\bar x(\mathrm{fam}_m) = \bar x'(\mathrm{fam}_m)$.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used here — schemes and `Spec`, `CategoryTheory.IsPullback`, `IsProper`, opens and presheaf sections, `Localization.Away` — but has no formal schemes and no Deligne data; the functor `AlgFunctor` on $\mathcal O$-algebras, the points of the formal upper half-plane, the vertex and edge chart rings and this levelwise notion of formal quotient are the project's own.
--
--   **Where it is used.** This structure is the interface through which the Čerednik–Drinfeld uniformisation enters the argument: a formal quotient datum presents $\Gamma \backslash (\hat\Omega \hat\otimes O^{nr})$ levelwise, so that its universal property can be matched against the $\pi$-adic completion of a Shimura curve. The resulting uniformisation feeds the study of the curve's reduction and component groups used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_FormalQuotientDatum.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree

namespace CerednikDrinfeld
namespace FormalOmega

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure FormalQuotientDatum
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ) (r : ℕ)
    {G : Type} [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ Γ' : Subgroup G)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Type 1 where

  Y : ℕ → Scheme.{0}

  yb : ∀ n : ℕ, Y n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))

  yt : ∀ n : ℕ, Y n ⟶ Y (n + 1)

  yt_isPullback : ∀ n : ℕ, IsPullback (yt n) (yb n) (yb (n + 1))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))))))

  yb_isProper : ∀ n : ℕ, IsProper (yb n)

  q : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 →
    (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Spec (CommRingCat.of B) ⟶ Y n)

  q_over : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
    (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
    q n B hB x ≫ yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))

  q_natural : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
    (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B' π) ^ (n + 1) = 0) (φ : B →ₐ[𝒪] B')
    (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
    q n B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ q n B hB x

  q_yt : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
    (hB' : (algebraMap 𝒪 B π) ^ (n + 1 + 1) = 0) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
    q (n + 1) B hB' x = q n B hB x ≫ yt n

  q_inv : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (γ : G), γ ∈ Γ →
    ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
      OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → q n B hB x' = q n B hB x

  q_fib : ∀ (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : (algebraMap 𝒪 k π) ^ (n + 1) = 0)
    (ψ : Onr →ₐ[𝒪] k),
    (∀ η : Spec (CommRingCat.of k) ⟶ Y n,
      η ≫ yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
        Spec.map (CommRingCat.ofHom (algebraMap 𝒪 k)) →
      ∃ P : (Omega K₀ π).obj k, q n k hk (ψ, P) = η) ∧
    ∀ P P' : (Omega K₀ π).obj k, q n k hk (ψ, P) = q n k hk (ψ, P') ↔
      ∃ γ ∈ Γ, OmegaNr.IsTwistedAct π Onr Fr vdet k (σ γ) (ψ, P) (ψ, P')

  univ : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B),
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x)) →
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
        OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → ρ' B hB x' = ρ' B hB x) →
    ∃ u : ∀ n : ℕ, Y n ⟶ T,
      (∀ n : ℕ, u n ≫ t = yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) ∧
      (∀ n : ℕ, yt n ≫ u (n + 1) = u n) ∧
      (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
        (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), q n B hB x ≫ u n = (ρ' B ⟨n + 1, hB⟩ x).1) ∧
      ∀ u' : ∀ n : ℕ, Y n ⟶ T,
        (∀ n : ℕ, u' n ≫ t = yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) →
        (∀ n : ℕ, yt n ≫ u' (n + 1) = u' n) →
        (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
          (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), q n B hB x ≫ u' n = (ρ' B ⟨n + 1, hB⟩ x).1) →
        u' = u

  Ynr : ℕ → Scheme.{0}

  p₁ : ∀ n : ℕ, Ynr n ⟶ Y n

  p₂ : ∀ n : ℕ, Ynr n ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))

  isPullback_nr : ∀ n : ℕ, IsPullback (p₁ n) (p₂ n)
    (yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))))
    (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))))

  jnr : ∀ n : ℕ, Ynr n ⟶ Ynr (n + 1)

  jnr_p₁ : ∀ n : ℕ, jnr n ≫ p₁ (n + 1) = p₁ n ≫ yt n

  jnr_p₂ : ∀ n : ℕ, jnr n ≫ p₂ (n + 1) = p₂ n ≫ Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 Onr π) (Nat.le_succ (n + 1))))))

  U : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), (Ynr n).Opens

  c : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
    ↑((Ynr n).presheaf.obj (Opposite.op (U h n))) →+* ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})

  κ : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) ⟶ Ynr n

  κ_preimage : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), (κ h n) ⁻¹ᵁ (U h n) = ⊤ ∧
        ∀ (hle : (⊤ : (Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))).Opens) ≤ (κ h n) ⁻¹ᵁ (U h n))
          (s : ↑((Ynr n).presheaf.obj (Opposite.op (U h n)))),
          c h n s = (Scheme.ΓSpecIso (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))).hom.hom
            ((Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))).presheaf.map (homOfLE hle).op (((κ h n).app (U h n)).hom s))

  c_const : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ) (y : Onr),
        c h n ((Ynr n).presheaf.map (homOfLE le_top).op
          ((p₂ n).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))).inv.hom
            (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) y)))) =
          Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) y)

  U_jnr : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
        U h n = (jnr n) ⁻¹ᵁ (U h (n + 1)) ∧
        ∀ (hle : U h n ≤ (jnr n) ⁻¹ᵁ (U h (n + 1))) (s : ↑((Ynr (n + 1)).presheaf.obj (Opposite.op (U h (n + 1))))),
          c h n ((Ynr n).presheaf.map (homOfLE hle).op (((jnr n).app (U h (n + 1))).hom s)) =
          Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
            (pow_dvd_pow (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) (Nat.le_succ (n + 1)))) (c h (n + 1) s)

  κ_p₁ : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ)
          (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
          (xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →ₐ[Onr] B) (d P : DeligneDatum (K := K₀) π B),
          (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
          DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
          Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ κ h n ≫ p₁ n = q n B hB ((IsScalarTower.toAlgHom 𝒪 Onr B), P)

  cover : ∀ n : ℕ, ⨆ h : Matrix.GeneralLinearGroup (Fin 2) K₀, U h n = ⊤

  functions : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀),
        (∀ (s s' : ∀ m : ℕ, ↑((Ynr m).presheaf.obj (Opposite.op (U h m)))),
          (∀ (m : ℕ) (hle : U h m ≤ (jnr m) ⁻¹ᵁ (U h (m + 1))),
              (Ynr m).presheaf.map (homOfLE hle).op (((jnr m).app (U h (m + 1))).hom (s (m + 1))) = s m) →
          (∀ (m : ℕ) (hle : U h m ≤ (jnr m) ⁻¹ᵁ (U h (m + 1))),
              (Ynr m).presheaf.map (homOfLE hle).op (((jnr m).app (U h (m + 1))).hom (s' (m + 1))) = s' m) →
          (∀ m : ℕ, c h m (s m) = c h m (s' m)) → s = s') ∧
        ∀ fam : ∀ m : ℕ, ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}), (∀ m : ℕ, Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
              (pow_dvd_pow (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) (Nat.le_succ (m + 1)))) (fam (m + 1)) = fam m) →
          ((∃ s : ∀ m : ℕ, ↑((Ynr m).presheaf.obj (Opposite.op (U h m))),
              (∀ (m : ℕ) (hle : U h m ≤ (jnr m) ⁻¹ᵁ (U h (m + 1))),
              (Ynr m).presheaf.map (homOfLE hle).op (((jnr m).app (U h (m + 1))).hom (s (m + 1))) = s m) ∧
              ∀ m : ℕ, c h m (s m) = fam m) ↔
            ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B],
              IsNilpotent (algebraMap 𝒪 B π) →
              ∀ (xbar xbar' : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) →ₐ[Onr] B) (d d' P P' : DeligneDatum (K := K₀) π B),
                (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
                (d'.line (stdFullLattice K₀) =
              Submodule.span B {(xbar' (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar' (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
                DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
                DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d' P' →
                (∃ γ ∈ Γ', DeligneDatum.IsPullback (K := K₀) (π := π) B (σ γ)⁻¹ P P') →
                xbar (fam m) = xbar' (fam m))

end FormalOmega
end CerednikDrinfeld


