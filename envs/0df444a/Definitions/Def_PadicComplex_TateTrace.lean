-- Prove2me | Definitions.Def_PadicComplex_TateTrace
-- name    : PadicComplex_TateTrace
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/60620f52-db83-54ac-a5f8-5afe83dbb3f7
-- title:
--   Tate normalised traces along a tower in Cp​
-- statement:
--   Fix a prime $p$ and work with $\overline{\mathbb{Q}}_p$ (`PadicAlgCl p`) and its completion $\mathbb{C}_p$, on which the group $\operatorname{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ acts by the isometric, continuous extension of its action on $\overline{\mathbb{Q}}_p$. Given a family $(K_m)_{m\in\mathbb{N}}$ of intermediate fields $\mathbb{Q}_p \subseteq K_m \subseteq \overline{\mathbb{Q}}_p$, [`PadicComplex.towerClosure p Km`](../def/PadicComplex_TateTrace.html#L12) is the subset $X \subseteq \mathbb{C}_p$ obtained as the topological closure of $\bigcup_m K_m$, each $K_m$ being viewed in $\mathbb{C}_p$ through $\overline{\mathbb{Q}}_p \hookrightarrow \mathbb{C}_p$; no monotonicity of the family is imposed, so in general $X$ is the closure of the union of the images, which in the intended applications is the closure of $K_\infty = \bigcup_m K_m$.
--
--   [`PadicComplex.IsTateTrace p Km m d R`](../def/PadicComplex_TateTrace.html#L15) is a predicate (a structure all of whose fields are propositions) on a level $m \in \mathbb{N}$, a real constant $d$ and an arbitrary function $R \colon \mathbb{C}_p \to \mathbb{C}_p$, asserting six conditions, all of which constrain $R$ only on $X =$ `towerClosure p Km`: $R$ is additive on $X$; $R(kx) = kR(x)$ for $k \in K_m$ and $x \in X$; $R(k) = k$ for every $k \in K_m$; for each $x \in X$ there is $k \in K_m$ with $R(x) = k$, so $R$ maps $X$ into $K_m$; $R(\sigma \cdot x) = R(x)$ for all $x \in X$ and all $\sigma$ in the fixing subgroup of $K_m$; and finally the estimate $\lVert x - R(x)\rVert \le d\,\lVert \sigma \cdot x - x\rVert$ for all $x \in X$ and every $\sigma$ fixing $K_m$ pointwise but not lying in the fixing subgroup of $K_{m+1}$. Thus $R$ behaves on $X$ as a $K_m$-linear projector onto $K_m$, commuting with the Galois action over $K_m$ and controlling the distance from $x$ to its projection by the displacement of $x$ under any such $\sigma$.
--
--   **Relation to Mathlib.** Mathlib has no notion of Tate normalised trace; this is the project's own predicate, phrased with Mathlib's `IntermediateField`, `fixingSubgroup`, topological `closure` and the norm on $\mathbb{C}_p$, together with the Galois action on $\mathbb{C}_p$ set up in the project's $p$-adic complex module.
--
--   **Where it is used.** The predicate packages the properties of Tate's normalised traces $p^{-n}\operatorname{Tr}_{K_{m+n}/K_m}$ in a tower of local fields, and serves as the interface through which ramification estimates feed into statements about Galois invariants and cohomology of $\mathbb{C}_p$ used in the $p$-adic Hodge-theoretic input to the proof.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_PadicComplex_TateTrace.lean

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

def towerClosure (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) : Set ℂ_[p] :=
  closure (⋃ m : ℕ, Set.range fun k : Km m => ((k : PadicAlgCl p) : ℂ_[p]))

structure IsTateTrace (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (m : ℕ) (d : ℝ)
    (R : ℂ_[p] → ℂ_[p]) : Prop where
  map_add : ∀ x ∈ towerClosure p Km, ∀ y ∈ towerClosure p Km, R (x + y) = R x + R y
  map_mul_left : ∀ (k : Km m), ∀ x ∈ towerClosure p Km,
    R (((k : PadicAlgCl p) : ℂ_[p]) * x) = ((k : PadicAlgCl p) : ℂ_[p]) * R x
  apply_coe : ∀ k : Km m, R ((k : PadicAlgCl p) : ℂ_[p]) = ((k : PadicAlgCl p) : ℂ_[p])
  exists_eq_coe : ∀ x ∈ towerClosure p Km, ∃ k : Km m, R x = ((k : PadicAlgCl p) : ℂ_[p])
  apply_smul : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (Km m).fixingSubgroup →
    ∀ x ∈ towerClosure p Km, R (σ • x) = R x
  norm_sub_apply_le : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (Km m).fixingSubgroup →
    σ ∉ (Km (m + 1)).fixingSubgroup → ∀ x ∈ towerClosure p Km, ‖x - R x‖ ≤ d * ‖σ • x - x‖

end PadicComplex

end


