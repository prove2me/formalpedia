-- Prove2me | Definitions.Def_GL2QFT_Supplement_Wreath
-- name    : GL2QFT_Supplement_Wreath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:38:20.750506+00:00
-- url     : https://prove2.me/theorems/89984f90-82a0-4ef9-800b-8dceb98a35f6
-- title:
--   Clifford data of the wreath product $F\wr S_n$ — base irreps, $I_\sigma$, the extension (248), $\tilde R_\nu$
-- statement:
--   The Clifford-theoretic data of §8.1–8.2 for $G=F\wr S_n=F^n\rtimes S_n$ (Definition 8.2: $(f,\pi)(f',\pi')=(f(\pi\cdot f'),\pi\pi')$, $(\pi\cdot f)_i=f_{\pi^{-1}(i)}$), using the platform's general wreath product `OddOrder.Isaacs.Ch03.WreathProduct`.
--
--   1. The base group $N=F^n\times\{1\}$ (226) and its irreps $R_\lambda(f)=\bigotimes_rR_{\lambda_r}(f_r)$, $\lambda\in\widehat F^n$ (230)–(232).
--   2. The inertia group $I_\sigma=N\rtimes H_\sigma$, $H_\sigma=\mathrm{Stab}_{S_n}(\sigma)$ for $(\pi)\lambda=(\lambda_{\pi^{-1}(1)},\dots,\lambda_{\pi^{-1}(n)})$ (233), (239)–(241).
--   3. The transport unitary $U_{\pi,\sigma}(v_1\otimes\dots\otimes v_n)=v_{\pi^{-1}(1)}\otimes\dots\otimes v_{\pi^{-1}(n)}$ (243) and the extension $R^{\rm ext}_\sigma(f,\pi)=R_\sigma(f)\,U_{(1_N,\pi),\sigma}$ (248).
--   4. For $\nu=(\nu_\rho)_\rho$ with $\nu_\rho\vdash n_\rho$ ($n_\rho$ the number of positions of $\rho$ in $\sigma$), the inflated little-group irrep $\tilde R_\nu(f,\pi)=\bigotimes_\rho R_{\nu_\rho}(\pi|_{\text{block }\rho})$ (249)–(251), the restriction to a block transported to $S_{n_\rho}$ along the increasing bijection.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Definition 8.2, eqs. (222)–(251), Definition 8.4, Observation 8.5, pp.66–69 (PDF pp.67–70)

import Definitions.Def_GL2QFT_Supplement_RepTheory
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_WreathProduct

noncomputable section

open Classical

namespace GL2QFT

namespace Supplement

namespace Wreath

open OddOrder.Isaacs.Ch03

variable (F : Type) [Group F] (n : ℕ)

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), Definition 8.2, eqs. (222)–(225), p.66
(PDF p.67): the wreath product `F ≀ S_n = F^n ⋊ S_n`, with `(f, π)(f′, π′) = (f (π · f′), ππ′)` and
`(π · f)_i = f_{π⁻¹(i)}`. This is the platform's general wreath product `F ≀[Fin n] S_n`
(`OddOrder.Isaacs.Ch03.WreathProduct`) for the natural action of `S_n` on `Fin n`. -/
abbrev WP : Type := WreathProduct F (Equiv.Perm (Fin n)) (Fin n)

instance [Fintype F] : Fintype (WP F n) := Fintype.ofFinite _

/-- arXiv:2608.28573, eq. (226), p.67 (PDF p.68): the base group `N = F^n × {1} ⊴ F ≀ S_n`. -/
abbrev baseGroup : Subgroup (WP F n) := (WreathProduct.inl : (Fin n → F) →* WP F n).range

variable {F n} {ΛF : Type} {BF : ΛF → Type} [∀ ρ, Fintype (BF ρ)] [∀ ρ, DecidableEq (BF ρ)]

/-- arXiv:2608.28573, eqs. (230)–(232), p.67 (PDF p.68): the irreducible representation of the base
group labelled by `λ = (λ_1, …, λ_n) ∈ F̂^n`, `R_λ(f) = ⊗_r R_{λ_r}(f_r)`, in the tensor-product
basis `|i_λ⟩ = ⊗_r |(i_r)_{λ_r}⟩`. -/
def baseRep (RF : ∀ ρ, F → Matrix (BF ρ) (BF ρ) ℂ) (l : Fin n → ΛF)
    (x : baseGroup F n) : Matrix (∀ r, BF (l r)) (∀ r, BF (l r)) ℂ :=
  tensorFamily fun r => RF (l r) ((x : WP F n).left r)

/-- arXiv:2608.28573, Definition 8.4 and eqs. (239)–(241), p.68 (PDF p.69): the inertia group
`I_σ = N ⋊ H_σ`, `H_σ = Stab_{S_n}(σ)`, for the action `(π)λ = (λ_{π⁻¹(1)}, …, λ_{π⁻¹(n)})` (233). -/
def inertiaW (σ : Fin n → ΛF) : Subgroup (WP F n) where
  carrier := {x | ∀ r, σ (x.right⁻¹ r) = σ r}
  one_mem' := by intro r; rfl
  mul_mem' := by
    intro x y hx hy r
    show σ ((x.right * y.right)⁻¹ r) = σ r
    rw [mul_inv_rev, Equiv.Perm.mul_apply, hy, hx]
  inv_mem' := by
    intro x hx r
    show σ (x.right⁻¹⁻¹ r) = σ r
    rw [inv_inv]
    have := hx (x.right r)
    simp at this
    exact this.symm

theorem inertiaW_inv_apply {σ : Fin n → ΛF} (x : inertiaW (F := F) σ) (r : Fin n) :
    σ ((x : WP F n).right⁻¹ r) = σ r := x.2 r

theorem inertiaW_apply {σ : Fin n → ΛF} (x : inertiaW (F := F) σ) (r : Fin n) :
    σ ((x : WP F n).right r) = σ r := by
  have := x.2 ((x : WP F n).right r)
  simp at this
  exact this.symm

/-- arXiv:2608.28573, eqs. (243) and (247), p.68 (PDF p.69): for `π ∈ H_σ` the transport unitary
`U_{π,σ}(v_1 ⊗ ⋯ ⊗ v_n) = v_{π⁻¹(1)} ⊗ ⋯ ⊗ v_{π⁻¹(n)}`, an endomorphism of `V_σ` since
`(π)σ = σ`: `U_{π,σ}|i⟩ = |j⟩` with `j_r = i_{π⁻¹(r)}`. -/
def transportU (σ : Fin n → ΛF) (x : inertiaW (F := F) σ) :
    Matrix (∀ r, BF (σ r)) (∀ r, BF (σ r)) ℂ :=
  Matrix.of fun j i =>
    if ∀ r, j r = cast (congrArg BF (inertiaW_inv_apply x r)) (i ((x : WP F n).right⁻¹ r))
    then 1 else 0

/-- arXiv:2608.28573, eq. (248), p.68 (PDF p.69): the extension
`R^ext_σ(f, π) := R_σ(f) U_{(1_N, π), σ}` of `R_σ` to `I_σ`. -/
def extRep (RF : ∀ ρ, F → Matrix (BF ρ) (BF ρ) ℂ) (σ : Fin n → ΛF) (x : inertiaW (F := F) σ) :
    Matrix (∀ r, BF (σ r)) (∀ r, BF (σ r)) ℂ :=
  (tensorFamily fun r => RF (σ r) ((x : WP F n).left r)) * transportU σ x

/-- The block of positions carrying the label `ρ` in `σ` (Observation 8.5): `{r : σ r = ρ}`; its
size is the multiplicity `n_ρ` of `ρ` in `σ`. -/
abbrev block (σ : Fin n → ΛF) (ρ : ΛF) : Type := {r : Fin n // σ r = ρ}

/-- arXiv:2608.28573, Observation 8.5, eq. (241), p.68 (PDF p.69): the restriction of `π ∈ H_σ` to
the block of `ρ`, transported to `S_{n_ρ}` along the increasing bijection `Fin n_ρ ≃ block`
("each factor permutes the positions within one consecutive block of equal labels"). -/
def blockPerm [LinearOrder ΛF] (σ : Fin n → ΛF) (ρ : ΛF) (x : inertiaW (F := F) σ) :
    Equiv.Perm (Fin (Fintype.card (block σ ρ))) :=
  let e : Fin (Fintype.card (block σ ρ)) ≃ block σ ρ :=
    (Fintype.orderIsoFinOfCardEq (block σ ρ) rfl).toEquiv
  let p : Equiv.Perm (block σ ρ) :=
    (x : WP F n).right.subtypePerm (p := fun r => σ r = ρ) (fun r => by rw [inertiaW_apply x r])
  (e.trans p).trans e.symm

variable {BS : ∀ m, Nat.Partition m → Type} [∀ m ν, Fintype (BS m ν)]
  [∀ m ν, DecidableEq (BS m ν)]

/-- arXiv:2608.28573, eqs. (249)–(251), p.69 (PDF p.70), inflated to `I_σ` (Definition 7.10): for a
tuple of partitions `ν = (ν_ρ)_ρ` with `ν_ρ ⊢ n_ρ`, `R̃_ν(f, π) = R_ν(π) = ⊗_ρ R_{ν_ρ}(π|_{block ρ})`.

**Formalization Note** The tuple is indexed by all `ρ ∈ F̂`; a label `ρ` that does not occur in `σ`
has `n_ρ = 0`, the unique partition of `0` and the one-dimensional trivial factor, so these tuples
are in bijection with the tuples `(ν_1, …, ν_ℓ)` of (249). -/
def littleRep [Fintype ΛF] [LinearOrder ΛF]
    (RS : ∀ m (ν : Nat.Partition m), Equiv.Perm (Fin m) → Matrix (BS m ν) (BS m ν) ℂ)
    (σ : Fin n → ΛF) (ν : ∀ ρ, Nat.Partition (Fintype.card (block σ ρ)))
    (x : inertiaW (F := F) σ) :
    Matrix (∀ ρ, BS _ (ν ρ)) (∀ ρ, BS _ (ν ρ)) ℂ :=
  tensorFamily fun ρ => RS _ (ν ρ) (blockPerm σ ρ x)

end Wreath

end Supplement

end GL2QFT


