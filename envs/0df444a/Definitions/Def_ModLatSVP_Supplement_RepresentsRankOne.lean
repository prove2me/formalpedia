-- Prove2me | Definitions.Def_ModLatSVP_Supplement_RepresentsRankOne
-- name    : ModLatSVP_Supplement_RepresentsRankOne
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:18:30.945495+00:00
-- url     : https://prove2.me/theorems/0fcb69f3-1695-49a7-a96f-cfd41cfee756
-- title:
--   Rank-one modules over a subfield of the chain, and the top level of a chain
-- statement:
--   Let $K$ be a number field with involution $\star=\tau$ and let $E\subseteq K$ be a subfield with an integral basis $\beta_1,\dots,\beta_e$ of $\mathcal O_E$. A **rank-one $\mathcal O_E$-module** in the input model of §2.2 is the lattice $\mathbb Z^e$ with a rational Gram matrix $G$ and integer matrices $A_1,\dots,A_e$, where $A_a$ describes multiplication by $\beta_a$ on coefficient columns. It is required that there be a ring homomorphism $\varphi:E\to M_e(\mathbb Q)$ with
--
--   1. $\varphi(\beta_a)=A_a$ for every $a$;
--   2. $G$ positive definite;
--   3. $\varphi(\alpha)^{T}G=G\,\varphi(\alpha^\star)$ for every $\alpha\in E$,
--
--   so that multiplication by $\alpha^\star$ is the adjoint of multiplication by $\alpha$. Since $e=[E:\mathbb Q]$, the module has rank one over $E$.
--
--   The **top level** of a chain $K=K_0\supsetneq K_1\supsetneq\cdots$ is $K$ itself, described by its degree $d$, its multiplication table, its involution matrix and the identity inclusion; with it, the levels $0,1,\dots,h$ of a supplied chain are described uniformly.
--
--   These are the inputs of the rank-one routines $\mathsf{SV}_j$ and $\mathsf{EN}_j$ of Theorem 3.1.
--
--   **Formalization Note** Compatibility is imposed on every pair $\alpha,\alpha'\in E$ with $\alpha'=\tau(\alpha)$, which avoids constructing the restriction of $\tau$ to $E$ ($\tau$ maps $E$ into itself by the base mission's lemma on subfields of totally real or CM fields).
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), §3.1, p.17 (PDF p.17): "For each 0 ≤ j ≤ h, we construct two routines on rank-one 𝒪_{K_j}-modules"; input model of §2.2, p.12

import Mathlib
import Definitions.Def_ModLatSVP_RepresentsChain

namespace ModLatSVP

namespace Supplement

/-- The top field `K₀ = K` of a chain, written as a level: its degree `d`, multiplication table `c`,
involution matrix `S`, and the identity inclusion (so `levelBasis ω (topLevel c S) = ω`). Kim, Lee, Son,
*Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027
submission (manuscript sha256 e7151fad…), §3.1, p.17. -/
def topLevel {d : ℕ} (c : Fin d → Fin d → Fin d → ℤ) (S : Matrix (Fin d) (Fin d) ℤ) : FieldLevel d :=
  ⟨d, c, S, 1⟩

/-- A rank-one module over `𝒪_E` for a subfield `E` of `K` (§3.1, p.17: "two routines on rank-one
𝒪_{K_j}-modules"; input model of §2.2, p.12). The lattice is `ℤ^e` with rational Gram matrix `G`, and
`A a` is the integer matrix of multiplication by the basis element `β a` of `𝒪_E` (column convention).
`RepresentsRankOne K τ E β G A` says that there is a ring homomorphism `φ : E →+* Mat_e(ℚ)` (the action
of `E` on `ℚ^e`) with
1. `φ(β a) = A a` for every `a`;
2. `G` positive definite;
3. `φ(α)ᵀ G = G φ(α⋆)` for all `α ∈ E`, where `α⋆ = τ α` (which lies in `E`).

**Formalization Note.** When `β` is an integral basis of `𝒪_E` and `e = [E : ℚ]` (the chain data give
both), `ℚ^e` is a one-dimensional `E`-vector space, so the module has rank one, and `φ` maps `𝒪_E` to
integer matrices. The compatibility is required for every pair `α, α'` of `E` with `α' = τ α`, which
avoids constructing the restriction of `τ` to `E`; that `τ` maps `E` into itself is
`ModLatSVP.subfield_star`. -/
def RepresentsRankOne (K : Type*) [Field K] [CharZero K] (τ : K ≃ₐ[ℚ] K)
    (E : IntermediateField ℚ K) {e : ℕ} (β : Fin e → K) (G : Matrix (Fin e) (Fin e) ℚ)
    (A : Fin e → Matrix (Fin e) (Fin e) ℤ) : Prop :=
  ∃ φ : E →+* Matrix (Fin e) (Fin e) ℚ,
    (∀ a, ∃ h : β a ∈ E, φ ⟨β a, h⟩ = (A a).map (fun z : ℤ => (z : ℚ))) ∧
    (G.map (fun q : ℚ => (q : ℝ))).PosDef ∧
    ∀ α α' : E, (α' : K) = τ α →
      ((φ α).map (fun q : ℚ => (q : ℝ))).transpose * G.map (fun q : ℚ => (q : ℝ)) =
        G.map (fun q : ℚ => (q : ℝ)) * (φ α').map (fun q : ℚ => (q : ℝ))

end Supplement

end ModLatSVP


