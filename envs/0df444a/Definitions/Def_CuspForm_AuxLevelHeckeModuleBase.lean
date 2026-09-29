-- Prove2me | Definitions.Def_CuspForm_AuxLevelHeckeModuleBase
-- name    : CuspForm_AuxLevelHeckeModuleBase
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/dd278f24-ff72-52b8-92c1-dea07bacfb80
-- title:
--   Base-level Hecke datum and its localised cohomology module
-- statement:
--   Throughout, $N\ge 1$ and $r$ are natural numbers, $S\subseteq\mathbb N$, and $\mathcal O$ is a commutative (for the later items, local) ring with residue field $k=\mathcal O/\mathfrak m_{\mathcal O}$. The carrier is $H^1(N,\top,\mathcal O)=\operatorname{Hom}(\Gamma_0(N)^{\mathrm{ab}},\mathcal O)$, the additive homomorphisms from the abelianisation (in `Additive` form) of $\Gamma_H(N,\top)=\Gamma_0(N)$ to $\mathcal O$. For a generator $g$ of the index set `Gen N r S` — a prime $\ell$ with $\ell\notin S$, $\ell\nmid N$ and $\ell\ne r$ — `baseOp` is the $\mathcal O$-linear endomorphism `heckeTL` of this carrier at $\ell$, namely $\varphi\mapsto\operatorname{cores}(\varphi\circ\mathrm{conjL}_\ell)$: restrict along the conjugation map $\begin{pmatrix}a&b\\c&d\end{pmatrix}\mapsto\begin{pmatrix}a&b/\ell\\ c\ell&d\end{pmatrix}$ defined on the finite-index subgroup of $\Gamma_0(N)$ with $\ell\mid b$, then apply the additive transfer back to $\Gamma_0(N)$. The predicate `BaseOpComm` asserts that these endomorphisms commute pairwise.
--
--   Given a ring homomorphism $\theta$ from the weight-two Hecke subalgebra [`CuspForm.heckeAlgebra N 2 S`](../def/CuspForm_HeckeAlgebra.html#L18) of $\operatorname{End}_{\mathbb C}S_2(\Gamma_0(N))$ to $k$ and a proof $hc_0$ of `BaseOpComm`, `baseHeckeData` assembles a [`CohCarrier.HeckeData`](../def/CohCarrier_HeckeData.html#L14) over $\mathcal O$ on this carrier with residue field $k$: generators `Gen N r S`, operators `baseOp`, commutativity field $hc_0$ (a theorem carried as data), and residual eigenvalues $g\mapsto\theta(T_\ell)$. An instance records the resulting action of the free algebra $\mathcal O[X_g]$ on the carrier, $X_g$ acting as `baseOp g`, and `baseML` is the associated localised module: the localisation of $H^1(N,\top,\mathcal O)$ at the complement of the prime ideal $\mathfrak m_\theta=\ker\big(\mathcal O[X_g]\to k,\;X_g\mapsto\theta(T_\ell)\big)$, an $\mathcal O$-module and an $\mathcal O[X_g]$-module compatibly. The module also records that the free algebra and the ideal $\mathfrak m_\theta$ here coincide with those of the auxiliary-level datum `heckeData N r S 𝒪 θ`, the generator set and residual eigensystem being the same.
--
--   **Relation to Mathlib.** The carrier, the transfer-theoretic Hecke operators on it and the `HeckeData` packaging are the project's own; the localisation and the polynomial algebra are Mathlib's `LocalizedModule` and `MvPolynomial`.
--
--   **Where it is used.** The localised module at level $N$ is the base-level counterpart of the auxiliary-level module attached to $\Gamma_0(N)\cap\Gamma_1(r)$ for a Taylor–Wiles auxiliary prime $r$; sharing the same free algebra and the same prime $\mathfrak m_\theta$ lets the two be compared over one and the same Hecke ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CuspForm_AuxLevelHeckeModuleBase.lean

import Definitions.Def_CuspForm_AuxLevelHeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace CuspForm.AuxLevel

def baseOp (N r : ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] (g : Gen N r S) :
    Module.End 𝒪 (CohCarrier.H1 N ⊤ 𝒪) :=
  haveI : NeZero g.ℓ := ⟨g.prime.ne_zero⟩
  CohCarrier.heckeTL N ⊤ 𝒪 g.ℓ

def BaseOpComm (N r : ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] : Prop :=
  ∀ g h : Gen N r S, baseOp N r S 𝒪 g * baseOp N r S 𝒪 h = baseOp N r S 𝒪 h * baseOp N r S 𝒪 g

def baseHeckeData (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₀ : BaseOpComm N r S 𝒪) :
    CohCarrier.HeckeData 𝒪 (CohCarrier.H1 N ⊤ 𝒪) (IsLocalRing.ResidueField 𝒪) where
  Gen := Gen N r S
  op := baseOp N r S 𝒪
  comm := hc₀
  θbar g := θ (CuspForm.heckeAlgebra.T g.prime g.not_dvd g.notMem)

instance instModuleFreeAlgBaseCarrier (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪]
    [IsLocalRing 𝒪] (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
    (hc₀ : BaseOpComm N r S 𝒪) :
    Module (baseHeckeData N r S 𝒪 θ hc₀).FreeAlg (CohCarrier.H1 N ⊤ 𝒪) :=
  (baseHeckeData N r S 𝒪 θ hc₀).moduleFreeAlg

abbrev baseML (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₀ : BaseOpComm N r S 𝒪) :
    Type :=
  (baseHeckeData N r S 𝒪 θ hc₀).ML

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₀ : BaseOpComm N r S 𝒪)
    (hc : OpComm N r S 𝒪) :
    (baseHeckeData N r S 𝒪 θ hc₀).FreeAlg = (heckeData N r S 𝒪 θ hc).FreeAlg := rfl

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₀ : BaseOpComm N r S 𝒪)
    (hc : OpComm N r S 𝒪) :
    (baseHeckeData N r S 𝒪 θ hc₀).mTheta = (heckeData N r S 𝒪 θ hc).mTheta := rfl

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₀ : BaseOpComm N r S 𝒪) :
    Module 𝒪 (baseML N r S 𝒪 θ hc₀) := by infer_instance

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₀ : BaseOpComm N r S 𝒪) :
    Module (baseHeckeData N r S 𝒪 θ hc₀).FreeAlg (baseML N r S 𝒪 θ hc₀) := by infer_instance

example (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₀ : BaseOpComm N r S 𝒪) :
    IsScalarTower 𝒪 (baseHeckeData N r S 𝒪 θ hc₀).FreeAlg (baseML N r S 𝒪 θ hc₀) := by infer_instance

end CuspForm.AuxLevel

end


