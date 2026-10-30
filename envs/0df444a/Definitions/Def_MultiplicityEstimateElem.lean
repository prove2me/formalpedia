-- Prove2me | Definitions.Def_MultiplicityEstimateElem
-- name    : MultiplicityEstimateElem
-- status  : Definition
-- author  : @carlok
-- created : 2026-10-29T06:04:25.362688+00:00
-- url     : https://prove2.me/theorems/06d76f73-85da-4674-abc8-c9200d75632e
-- title:
--   The elementary multiplicity estimate: DALAG Th. 8.1 for $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ and $G^- = \{e\}$, in coordinates
-- statement:
--   Let $A_0, A_1, B_0, B_1$ be finite sets and $d = |A_0| + |A_1|$. Let $w_b = (w'_b, w''_b) \in \mathbb{C}^{A_0} \times \mathbb{C}^{A_1}$ ($b \in B_0$), with span $W$; let $u_j \in \mathbb{C}^{A_0}$ and non-zero $a_{ji} \in \mathbb{C}$ ($j \in B_1$, $i \in A_1$); and let $D_0, D_1 \geq 1$ and $M_0, M_1 \in \mathbb{N}$. For a weight vector $t$ on $A_1$, $\mathrm{Op}^t_w$ is the operator $\sum_{h \in A_0} w'_h\,\partial/\partial X_h + \sum_{i \in A_1} w''_i t_i$ on polynomials in the $X_h$ ($h \in A_0$). The columns are the $\lambda = (\tau, t)$ with $\tau \in \{0, \dots, D_0\}^{A_0}$ and $t \in \{-D_1, \dots, D_1\}^{A_1}$. For $r \in \mathbb{N}$, $k_1, \dots, k_r \in B_0$ and $s \in \mathbb{Z}^{B_1}$ put $E_{(r,k,s),(\tau,t)} = (\mathrm{Op}^t_{w_{k_1}} \cdots \mathrm{Op}^t_{w_{k_r}} X^\tau)(\sum_j s_j u_j) \cdot \prod_i (\prod_j a_{ji}^{s_j})^{t_i}$; this is the value of $D_{w_{k_1}} \cdots D_{w_{k_r}}(X^\tau Y^t)$ at the point $g_s = (\sum_j s_j u_j, (\prod_j a_{ji}^{s_j})_i)$, for the invariant derivations $D_w$ of DALAG §8.1.
--
--   The proposition `MultiplicityEstimateElem` states: for all such data and every non-zero vector $c$ on the columns, if $\sum_\lambda c_\lambda E_{(r,k,s),\lambda} = 0$ for every $r \leq dM_0$, every $k_1, \dots, k_r \in B_0$ and every $s$ with $|s_j| \leq dM_1$, then there are a subspace $V \subseteq \mathbb{C}^{A_0}$, integer vectors $\varphi_1, \dots, \varphi_q \in \mathbb{Z}^{A_1}$ with common complex kernel $L$, and $\ell \in \mathbb{N}$ with $\ell + \dim(W \cap (V \times L)) = \dim W$, such that $\dim V + \dim L < d$ and every set $R$ of vectors $s \in \mathbb{Z}^{B_1}$ with $|s_j| \leq M_1$ that are pairwise incongruent modulo $(V, \varphi)$ satisfies $\binom{M_0 + \ell}{\ell}\, |R|\, D_0^{\dim V} D_1^{\dim L} \leq 2^{d(d+1)/2}\, d!\, 2^{|A_1|}\, |A_0|^{|A_0|}\, D_0^{|A_0|} D_1^{|A_1|}$. Here $s, s' \in \mathbb{Z}^{B_1}$ are congruent modulo $(V, \varphi)$ when $\sum_j (s_j - s'_j) u_j \in V$ and $\prod_i (\prod_j a_{ji}^{s_j - s'_j})^{\varphi_{k,i}} = 1$ for every $k$.
--
--   In the language of DALAG Th. 8.1: $P = \sum_{(\tau, t)} c_{(\tau, t)} X^\tau Y^t$ is a non-zero element of $\mathbb{C}[G]$ for $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$, of degree at most $|A_0| D_0$ in $X$ and at most $D_1$ in each $Y_i$; the premise says that $P$ vanishes to order $> dM_0$ along $W$ at every point of $\Sigma[d]$, where $\Sigma = \{g_s : |s_j| \leq M_1\}$; $V \times L$ is the tangent space of the obstruction subgroup $G^* = V \times T_\Phi$ (DALAG §5.3.1), $\ell$ is $\ell'_0$, and $|R|$ is at most $\mathrm{Card}((\Sigma + G^*)/G^*)$. The proposition is meant as the case $G^- = \{e\}$, $G^+ = G$, $S_0 = M_0$ of Th. 8.1, with the Hilbert function of $G^*$ bounded below and that of $G$ bounded above through the explicit formula of DALAG Prop. 5.14. Only the proposition is defined here; its derivation from Th. 8.1 is not proved formally.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 8.1 (§8.1, p. 232; Chapter 8 is by D. Roy), the case G⁻ = {e}, G⁺ = G, written in coordinates; the Hilbert functions through Prop. 5.14 (§5.3.3). For G⁻ = {e} and finite Σ, DALAG notes that Th. 8.1 is a special case of Th. 2.1 of P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bull. Soc. Math. France 114 (1986), 355–383. C1.4 of the Diaz modulus mission. Statement in coordinates: 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- The elementary multiplicity estimate: the case `G⁻ = {e}`, `G⁺ = G` of Philippon's multiplicity estimate,
DALAG Th. 8.1 (M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer 2000, §8.1, p. 232;
chapter 8 by D. Roy), for `G = 𝔾ₐ^{A₀} × 𝔾ₘ^{A₁}` over `ℂ`, written in coordinates. It is a proposition, stated
here and not proved.

Data: finite types `A₀, A₁` (coordinates of `𝔾ₐ` and `𝔾ₘ`), `B₀` (a family `wₑ` spanning the subspace `W` of
`ℂ^{A₀} × ℂ^{A₁}` along which one differentiates) and `B₁` (generators `(uₑ j, aₑ j)` of the point set
`Σ = {(Σ_j s_j uₑ j, Π_j (aₑ j)^{s_j}) : |s_j| ≤ M₁}`, with every `aₑ j i ≠ 0`); naturals `D₀, D₁ ≥ 1`, `M₀, M₁`;
and a nonzero coefficient vector `cₑ` on the exponents `(τ, t)`, `τ_h ≤ D₀`, `t_i ∈ [-D₁, D₁]` (entry `t_i + D₁`), that
is, the polynomial `P = Σ cₑ(τ, t) X^τ Y^t`.

Premise: `P` vanishes to order `> d·M₀` along `W` at every point of `Σ[d]`, `d = |A₀| + |A₁|`. In coordinates, for every
`r ≤ d·M₀`, every `k : Fin r → B₀` and every `s` with `|s_j| ≤ d·M₁`,
`Σ_{(τ,t)} cₑ(τ,t) · (Op_{wₑ (k 1)} ⋯ Op_{wₑ (k r)} X^τ)(Σ_j s_j uₑ j) · Π_i (Π_j aₑ j i ^ s_j)^{t_i} = 0`, where
`Op_w = Σ_h w.1 h ∂/∂X_h + (Σ_i w.2 i · t_i) id` is the derivation `D_w` of DALAG §8.1 acting on `X^τ Y^t`.

Conclusion: there are a subspace `Vₑ ≤ ℂ^{A₀}` and integer vectors `φₑ k ∈ ℤ^{A₁}` with common complex kernel `Lₑ`
(the obstruction subgroup `G* = Vₑ × T_Φ`, recorded only through `(Vₑ, φₑ)`), and `ℓₑ` with
`ℓₑ + dim (W ⊓ Vₑ × Lₑ) = dim W`, such that `dim Vₑ + dim Lₑ < d` and every set `Rₑ` of vectors in the box
`|s_j| ≤ M₁` that are pairwise incongruent modulo `(Vₑ, φₑ)` satisfies
`C(M₀ + ℓₑ, ℓₑ) · |Rₑ| · D₀^{dim Vₑ} · D₁^{dim Lₑ} ≤ 2^{d(d+1)/2} · d! · 2^{|A₁|} · |A₀|^{|A₀|} · D₀^{|A₀|} · D₁^{|A₁|}`.
This is Th. 8.1's inequality `C(S₀ + ℓ₀′, ℓ₀′) · Card((Σ + G*)/G*) · H(G*; D₀, D) ≤ H(G⁺; D₀, D)` with `S₀ = M₀`, the
Hilbert function of `G*` bounded below and that of `G⁺ = G` bounded above (DALAG Prop. 5.14). -/
def MultiplicityEstimateElem : Prop :=
  ∀ (A₀ A₁ B₀ B₁ : Type) [Fintype A₀] [Fintype A₁] [Fintype B₀] [Fintype B₁]
      [DecidableEq A₀] [DecidableEq A₁]
      (wₑ : B₀ → (A₀ → ℂ) × (A₁ → ℂ)) (uₑ : B₁ → A₀ → ℂ) (aₑ : B₁ → A₁ → ℂ) (D₀ D₁ M₀ M₁ : ℕ)
      (cₑ : (A₀ → Fin (D₀ + 1)) × (A₁ → Fin (2 * D₁ + 1)) → ℂ),
      1 ≤ D₀ → 1 ≤ D₁ → (∀ j i, aₑ j i ≠ 0) → cₑ ≠ 0 →
      (∀ (rₑ : ℕ) (kₑ : Fin rₑ → B₀) (sₑ : B₁ → ℤ), rₑ ≤ (Fintype.card A₀ + Fintype.card A₁) * M₀ → (∀ j, |sₑ j| ≤ (((Fintype.card A₀ + Fintype.card A₁) * M₁ : ℕ) : ℤ)) →
        ∑ l, cₑ l * (MvPolynomial.eval (∑ j, ((sₑ j : ℤ) : ℂ) • uₑ j)
          ((List.ofFn fun k : Fin rₑ =>
            ((∑ h, (wₑ (kₑ k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (wₑ (kₑ k)).2 i * (((l.2 i : ℕ) : ℂ) - D₁)) • LinearMap.id :
                Module.End ℂ (MvPolynomial A₀ ℂ)))).prod
            (∏ h, MvPolynomial.X h ^ (l.1 h : ℕ)))
        * ∏ i, (∏ j, aₑ j i ^ sₑ j) ^ (((l.2 i : ℕ) : ℤ) - D₁)) = 0) →
      ∃ (Vₑ : Submodule ℂ (A₀ → ℂ)) (qₑ : ℕ) (φₑ : Fin qₑ → A₁ → ℤ) (Lₑ : Submodule ℂ (A₁ → ℂ)) (ℓₑ : ℕ),
        (∀ vₑ, vₑ ∈ Lₑ ↔ ∀ k, ∑ i, (φₑ k i : ℂ) * vₑ i = 0) ∧
        ℓₑ + Module.finrank ℂ ↥(Submodule.span ℂ (Set.range wₑ) ⊓ Vₑ.prod Lₑ)
          = Module.finrank ℂ ↥(Submodule.span ℂ (Set.range wₑ)) ∧
        Module.finrank ℂ ↥Vₑ + Module.finrank ℂ ↥Lₑ < Fintype.card A₀ + Fintype.card A₁ ∧
        ∀ Rₑ : Finset (B₁ → ℤ), (∀ s ∈ Rₑ, ∀ j, |s j| ≤ (M₁ : ℤ)) →
          (∀ s ∈ Rₑ, ∀ s' ∈ Rₑ,
            ((∑ j, ((s j - s' j : ℤ) : ℂ) • uₑ j) ∈ Vₑ ∧
              ∀ k, ∏ i, (∏ j, aₑ j i ^ (s j - s' j)) ^ φₑ k i = 1) → s = s') →
          (M₀ + ℓₑ).choose ℓₑ * Rₑ.card * D₀ ^ Module.finrank ℂ ↥Vₑ * D₁ ^ Module.finrank ℂ ↥Lₑ
            ≤ (2 ^ ((Fintype.card A₀ + Fintype.card A₁) * (Fintype.card A₀ + Fintype.card A₁ + 1) / 2)
            * (Fintype.card A₀ + Fintype.card A₁).factorial * 2 ^ Fintype.card A₁
            * Fintype.card A₀ ^ Fintype.card A₀) * D₀ ^ Fintype.card A₀ * D₁ ^ Fintype.card A₁

end DiazModulus


