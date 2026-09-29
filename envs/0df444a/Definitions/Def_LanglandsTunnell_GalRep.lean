-- Prove2me | Definitions.Def_LanglandsTunnell_GalRep
-- name    : LanglandsTunnell_GalRep
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/4e9e9dd1-118c-5a3d-8b57-96120377af89
-- title:
--   Galois representation attached to a GL2​(F3​)-realisation, and relative degree
-- statement:
--   Throughout, $L$ is a number field that is Galois over $\mathbb{Q}$, equipped with an $L$-algebra structure on $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` compatible with the $\mathbb{Q}$-structures (a scalar tower $\mathbb{Q} \subseteq L \subseteq \overline{\mathbb{Q}}$), and $\Gamma_{\mathbb{Q}}$ denotes the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$.
--
--   Given a group isomorphism $e \colon \mathrm{Gal}(L/\mathbb{Q}) \xrightarrow{\ \sim\ } \mathrm{GL}_2(\mathbb{Z}/3)$, the definition `galRep e` is the monoid homomorphism $\Gamma_{\mathbb{Q}} \to \mathrm{GL}_2(\mathbb{Z}/3)$ obtained by restricting an automorphism of $\overline{\mathbb{Q}}$ to the normal subextension $L$ (Mathlib's `AlgEquiv.restrictNormalHom`) and then applying $e$; the companion lemma `galRep_apply` records that evaluating `galRep e` at $\sigma$ is exactly $e$ applied to the restriction of $\sigma$ to $L$, so that the homomorphism factors through $\mathrm{Gal}(L/\mathbb{Q})$ by construction. The matrices are taken over $\mathbb{Z}/3$, i.e. over $\mathbb{F}_3$. No continuity, surjectivity, irreducibility or determinant condition is part of the definition; the existence of such a field $L$ and of such an $e$ are hypotheses supplied elsewhere.
--
--   Independently, `IsRelDegree H σ n` is a predicate on a subgroup $H$ of an arbitrary group $G$, an element $\sigma \in G$ and a natural number $n$: it asserts that $n > 0$, that $\sigma^n \in H$, and that $\sigma^m \notin H$ for every $m$ with $0 < m < n$. Thus $n$ is the least positive exponent carrying $\sigma$ into $H$; nothing is asserted about the order of $\sigma$, the index of $H$, or any identification of $n$ with a residue degree, and for $\sigma$ no positive power of which lies in $H$ the predicate holds for no $n$. The lemma `isRelDegree_one_top` is the degenerate instance: for $H = G$ the whole group, every $\sigma$ has relative degree $1$.
--
--   **Relation to Mathlib.** The restriction map $\Gamma_{\mathbb{Q}} \to \mathrm{Gal}(L/\mathbb{Q})$ is Mathlib's `AlgEquiv.restrictNormalHom`; `IsRelDegree` is the project's own group-theoretic formulation of a least positive exponent landing in a subgroup.
--
--   **Where it is used.** These definitions serve the Langlands–Tunnell input to the modularity argument, where a mod $3$ representation of $\Gamma_{\mathbb{Q}}$ with values in $\mathrm{GL}_2(\mathbb{F}_3)$ is presented through a Galois number field $L$ realising $\mathrm{GL}_2(\mathbb{F}_3)$ as its Galois group, and where local data at unramified primes are read off as relative degrees of Frobenius elements with respect to subgroups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_GalRep.lean

import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace LanglandsTunnell

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
  [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower ℚ L (AlgebraicClosure ℚ)]

noncomputable def galRep (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Γℚ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  e.toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) L)

@[simp] theorem galRep_apply (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (σ : Γℚ) :
    galRep e σ = e (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) L σ) := rfl

def IsRelDegree {G : Type*} [Group G] (H : Subgroup G) (σ : G) (n : ℕ) : Prop :=
  0 < n ∧ σ ^ n ∈ H ∧ ∀ m : ℕ, 0 < m → m < n → σ ^ m ∉ H

theorem isRelDegree_one_top {G : Type*} [Group G] (σ : G) : IsRelDegree (⊤ : Subgroup G) σ 1 :=
  ⟨Nat.one_pos, trivial, fun m _ hm => absurd hm (by omega)⟩

end LanglandsTunnell


