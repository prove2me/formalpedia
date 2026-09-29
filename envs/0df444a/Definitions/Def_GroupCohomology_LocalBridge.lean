-- Prove2me | Definitions.Def_GroupCohomology_LocalBridge
-- name    : GroupCohomology_LocalBridge
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/4d6798ec-47db-5e8a-9539-7d27bf9c2053
-- title:
--   Pinning predicates for local Ext-to-cohomology bridge maps
-- statement:
--   Fix a group $H$ together with a homomorphism $r\colon H\to\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (the "level" map used to define level-constant cochains), a homomorphism $\pi\colon H\to D$, objects $R,P,B,X$ of $\mathrm{Rep}\,\mathbb Z\,D$ with morphisms $f\colon R\to P$ and $g\colon P\to B$, an $H$-representation $A$ over $\mathbb Z$ with an additive map $\iota\colon X\to A$ (no equivariance required), a natural number $p$, an object $M$ of $\mathrm{Rep}\,(\mathbb Z/p)\,H$, and a biadditive pairing $\kappa\colon B\to(M\to A)$. Throughout, $(\mathrm{ihom}(\mathrm{Rep.res}\,\pi\,P)).\mathrm{obj}\,A$ is the internal hom in $\mathrm{Rep}\,\mathbb Z\,H$, i.e. the additive maps $P\to A$ with $(s\cdot\psi)(x)=s\cdot\psi(\pi(s)^{-1}x)$.
--
--   `IsLocalBridge₁` is a predicate on an additive map $\Lambda\colon (R\to X)_D\to H^1(H,M)$: it asserts that for every $D$-morphism $\varphi\colon R\to X$, every additive $\psi\colon P\to A$ with $\psi\circ f=\iota\circ\varphi$ on $R$, and every $n\colon H\to M$ satisfying $\kappa(g(x))(n(h))=\big((d_{01}\psi)(h)\big)(x)$ for all $h\in H$, $x\in P$, if $n$ lies in `cocycles₁ M` then $\Lambda(\varphi)$ is the class of $n$.
--
--   `IsLocalBridge₂` is the analogous predicate on an additive map $\Lambda\colon H^1(D,\mathrm{ihom}(R,X))\to$ `continuousH2 r M`: for every $1$-cocycle $a\colon D\to\mathrm{ihom}(R,X)$, every family $\psi\colon D\to\mathrm{Hom}(P,A)$ with $\psi_d\circ f=\iota\circ a(d)$, subject to the requirement that there be an intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$, finite-dimensional over $\mathbb Q$, such that every $s\in H$ with $r(s)$ in the fixing subgroup of $F$ fixes all values $\psi_d(x)$, and every $m\colon H\times H\to M$ with $\kappa(g(x))(m(h_1,h_2))=\big((d_{12}(\psi\circ\pi))(h_1,h_2)\big)(x)$, if $m$ lies in `levelCocycles₂ r M` (a $2$-cocycle, level-constant for some finite level) then $\Lambda$ of the class of $a$ is the class of $m$ in the quotient `continuousH2 r M`.
--
--   Both are pinning conditions on a given $\Lambda$ relative to the chosen presentation $R\to P\to B$ and pairing $\kappa$: they constrain $\Lambda$ exactly on those inputs admitting a lift $\psi$ and a compatible cochain, and say nothing about existence of such data, nor about independence of the choices.
--
--   **Relation to Mathlib.** `H1`, `cocycles₁`, `d₀₁`, `d₁₂`, `ihom` and `Rep.res` are Mathlib's; the level-constancy conditions, the quotient `continuousH2` and its projection, and the two bridge predicates are the project's own.
--
--   **Where it is used.** In the intended instantiation $H$ is the absolute Galois group of a local field $\mathbb Q_q$, $D$ the Galois group of a finite level $F_w/\mathbb Q_q$, $X=F_w^\times$, $A=\overline{\mathbb Q}_q^\times$, and $R\to P\to B$ a presentation of a finite coefficient module paired with $M$ by $\kappa$; the predicates then characterise the maps $\mathrm{Ext}^r_D(B,X)\to H^r(H,M)$ for $r=1,2$ that enter the local duality computations for the Selmer and deformation conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_LocalBridge.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace groupCohomology

variable {H : Type} [Group H] (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  {D : Type} [Group D] (π : H →* D)
  {R P B : Rep ℤ D} (f : R ⟶ P) (g : P ⟶ B)
  {X : Rep ℤ D} {A : Rep ℤ H} (ι : X →+ A)
  {p : ℕ} {M : Rep (ZMod p) H} (κ : B →+ M →+ A)

def IsLocalBridge₁ (Λ : (R ⟶ X) →+ H1 M) : Prop :=
  ∀ (φ : R ⟶ X) (ψ : (ihom (Rep.res π P)).obj A)
    (_ : ∀ x : R, LinearMap.toAddMonoidHom ψ (f.hom x) = ι (φ.hom x))
    (n : H → M)
    (_ : ∀ (h : H) (x : P), κ (g.hom x) (n h) = LinearMap.toAddMonoidHom ((d₀₁ ((ihom (Rep.res π P)).obj A)).hom ψ h) x)
    (hn : n ∈ cocycles₁ M),
    Λ φ = (H1π M).hom ⟨n, hn⟩

def IsLocalBridge₂ (Λ : H1 ((ihom R).obj X) →+ continuousH2 r M) : Prop :=
  ∀ (a : cocycles₁ ((ihom R).obj X)) (ψ : D → (ihom (Rep.res π P)).obj A)
    (_ : ∀ (d : D) (x : R), LinearMap.toAddMonoidHom (ψ d) (f.hom x) = ι (LinearMap.toAddMonoidHom ((a : D → (ihom R).obj X) d) x))
    (_ : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : H, r s ∈ F.fixingSubgroup → ∀ (d : D) (x : P), A.ρ s (LinearMap.toAddMonoidHom (ψ d) x) = LinearMap.toAddMonoidHom (ψ d) x)
    (m : H × H → M)
    (_ : ∀ (g₁ g₂ : H) (x : P), κ (g.hom x) (m (g₁, g₂)) =
      LinearMap.toAddMonoidHom ((d₁₂ ((ihom (Rep.res π P)).obj A)).hom (ψ ∘ π) (g₁, g₂)) x)
    (hm : m ∈ levelCocycles₂ r M),
    Λ ((H1π ((ihom R).obj X)).hom a) = continuousH2π r M ⟨m, hm⟩

end groupCohomology

end


