-- Prove2me | Definitions.Def_TensorIso233_BQP_Bilinear
-- name    : TensorIso233_BQP_Bilinear
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:38.608023+00:00
-- url     : https://prove2.me/theorems/5b5de8fc-fe71-4cdd-a762-90742ed482e3
-- title:
--   Unused directions, saturated output span and reduced maps of a bilinear map (2.5)–(2.6)
-- statement:
--   Let $\mu:E\times F\to G$ be a $\mathbb Z$-bilinear map with $E=\mathbb Z^e$, $F=\mathbb Z^f$, $G=\mathbb Z^g$. A sublattice $K\subseteq\mathbb Z^n$ is **saturated** if $mv\in K$ with $0\neq m\in\mathbb Z$ and $v\in\mathbb Z^n$ implies $v\in K$. The **unused second-input directions** and the **saturated output span** are (2.5)
--
--   $$
--   K=\{v\in F:\mu(E,v)=0\},\qquad H=\operatorname{span}_{\mathbb Q}\mu(E,F)\cap G .
--   $$
--
--   The **reduced map** (2.6) is the bilinear map $\bar\mu:E\times(F/K)\to H$ induced by $\mu$. Two bilinear maps $\mu:E\times F\to G$ and $\mu':E'\times F'\to G'$ are **integrally isomorphic** if there are $\mathbb Z$-linear isomorphisms $S:E\to E'$, $Q:F\to F'$, $P:G\to G'$ with $P\mu(u,v)=\mu'(Su,Qv)$ for all $u,v$, as in (2.4).
--
--   These notions are used to delete unused input and output directions of a tensor (Lemma 3.2).
--
--   **Formalization Note** $H$ is the preimage in $\mathbb Z^g$ of the $\mathbb Q$-span of the values of $\mu$ under the inclusion $\mathbb Z^g\subset\mathbb Q^g$. The reduced map is built from $\mu$ by restricting its codomain to $H$ and passing to the quotient by $K$.
-- source:
--   Thomas Huffstutler, Integral 2 × 3 × 3 Tensor Isomorphism is in BQP, STOC 2027 submission #319 (October 2026), §2.2, p. 13, (2.5)–(2.6); §2.1, p. 13, (2.4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/319.pdf

import Mathlib

/-!
# Bilinear maps of free abelian groups, unused directions and reduced maps

Thomas Huffstutler, *Integral 2 × 3 × 3 Tensor Isomorphism is in BQP*, STOC 2027 submission #319
(October 2026), §2.2, p. 13, (2.5)–(2.6), and §3.2, p. 14.

A bilinear map `μ : E × F → G` with `E = ℤᵉ`, `F = ℤᶠ`, `G = ℤᵍ` is a `ℤ`-bilinear map
`E →ₗ F →ₗ G`.
-/

namespace TensorIso233.BQP

/-- §2.2, p. 13: a sublattice `K ⊆ ℤⁿ` is saturated if `m v ∈ K` with `0 ≠ m ∈ ℤ`, `v ∈ ℤⁿ`,
implies `v ∈ K`. -/
def IsSaturated {n : ℕ} (K : Submodule ℤ (Fin n → ℤ)) : Prop :=
  ∀ (m : ℤ) (v : Fin n → ℤ), m ≠ 0 → m • v ∈ K → v ∈ K

/-- The inclusion `ℤⁿ → ℚⁿ` as a `ℤ`-linear map. -/
def castQ (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℚ) where
  toFun w i := (w i : ℚ)
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp

/-- (2.5), p. 13: the unused second-input directions `K = {v ∈ F : μ(E, v) = 0}`. -/
def unusedDirs {e f g : ℕ} (μ : (Fin e → ℤ) →ₗ[ℤ] (Fin f → ℤ) →ₗ[ℤ] (Fin g → ℤ)) :
    Submodule ℤ (Fin f → ℤ) :=
  LinearMap.ker μ.flip

/-- (2.5), p. 13: the saturated output span `H = span_ℚ μ(E, F) ∩ G`, the integer vectors of
`ℤᵍ` lying in the rational span of all values `μ(u, v)`. -/
def satSpan {e f g : ℕ} (μ : (Fin e → ℤ) →ₗ[ℤ] (Fin f → ℤ) →ₗ[ℤ] (Fin g → ℤ)) :
    Submodule ℤ (Fin g → ℤ) :=
  Submodule.comap (castQ g)
    ((Submodule.span ℚ (Set.range fun p : (Fin e → ℤ) × (Fin f → ℤ) => castQ g (μ p.1 p.2))).restrictScalars ℤ)

lemma mem_satSpan {e f g : ℕ} (μ : (Fin e → ℤ) →ₗ[ℤ] (Fin f → ℤ) →ₗ[ℤ] (Fin g → ℤ))
    (u : Fin e → ℤ) (v : Fin f → ℤ) : μ u v ∈ satSpan μ := by
  show castQ g (μ u v) ∈ Submodule.span ℚ _
  exact Submodule.subset_span ⟨(u, v), rfl⟩

/-- `μ` with its values regarded in the saturated output span `H`. -/
def toSatSpan {e f g : ℕ} (μ : (Fin e → ℤ) →ₗ[ℤ] (Fin f → ℤ) →ₗ[ℤ] (Fin g → ℤ)) :
    (Fin e → ℤ) →ₗ[ℤ] (Fin f → ℤ) →ₗ[ℤ] satSpan μ :=
  LinearMap.mk₂ ℤ (fun u v => ⟨μ u v, mem_satSpan μ u v⟩)
    (fun u₁ u₂ v => Subtype.ext (by change μ (u₁ + u₂) v = μ u₁ v + μ u₂ v; simp))
    (fun c u v => Subtype.ext (by change μ (c • u) v = c • μ u v; rw [map_smul, LinearMap.smul_apply]))
    (fun u v₁ v₂ => Subtype.ext (by change μ u (v₁ + v₂) = μ u v₁ + μ u v₂; simp))
    (fun c u v => Subtype.ext (by change μ u (c • v) = c • μ u v; rw [map_smul]))

/-- (2.6), p. 13: the reduced map `μ̄ : E × (F/K) → H`, induced by `μ` on the quotient by the
unused directions, with values in the saturated output span. -/
def reduce {e f g : ℕ} (μ : (Fin e → ℤ) →ₗ[ℤ] (Fin f → ℤ) →ₗ[ℤ] (Fin g → ℤ)) :
    (Fin e → ℤ) →ₗ[ℤ] ((Fin f → ℤ) ⧸ unusedDirs μ) →ₗ[ℤ] satSpan μ :=
  ((unusedDirs μ).liftQ (toSatSpan μ).flip (by
    intro v hv
    simp only [unusedDirs, LinearMap.mem_ker] at hv
    simp only [LinearMap.mem_ker]
    refine LinearMap.ext fun u => Subtype.ext ?_
    have := LinearMap.congr_fun hv u
    simpa [toSatSpan] using this)).flip

/-- §2.1 (2.4) and §3.2: integral isomorphism of bilinear maps `μ : E × F → G` and
`μ' : E' × F' → G'`: `ℤ`-linear isomorphisms `S : E ≃ E'`, `Q : F ≃ F'`, `P : G ≃ G'` with
`P μ(u, v) = μ'(S u, Q v)` for all `u, v`. -/
def IsoBilin {E F G E' F' G' : Type*}
    [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
    [AddCommGroup E'] [AddCommGroup F'] [AddCommGroup G']
    (μ : E →ₗ[ℤ] F →ₗ[ℤ] G) (μ' : E' →ₗ[ℤ] F' →ₗ[ℤ] G') : Prop :=
  ∃ (S : E ≃ₗ[ℤ] E') (Q : F ≃ₗ[ℤ] F') (P : G ≃ₗ[ℤ] G'),
    ∀ u v, P (μ u v) = μ' (S u) (Q v)

end TensorIso233.BQP


