-- Prove2me | Definitions.Def_HScattered_Delsarte_DelsarteSetting
-- name    : HScattered_Delsarte_DelsarteSetting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:13.741484+00:00
-- url     : https://prove2.me/theorems/1215cade-7b3c-4839-b860-e1862b54d825
-- title:
--   The setting of §3 and the Delsarte dual Ū = W + Γ^⊥ (Definition 3.2)
-- statement:
--   Let $\mathbb F_q\subseteq\mathbb F_{q^n}$ be finite fields and let $\mathbb V$ be a $k$-dimensional $\mathbb F_{q^n}$-vector space. The **setting of §3** consists of the following data.
--
--   1. $\mathbb F_{q^n}$-subspaces $\Lambda$ and $\Gamma$ of $\mathbb V$ with $\mathbb V=\Lambda\oplus\Gamma$; write $r=\dim_{\mathbb F_{q^n}}\Lambda$, so $\Lambda=V(r,q^n)$ and $\dim\Gamma=k-r$.
--   2. A $k$-dimensional $\mathbb F_q$-subspace $W$ of $\mathbb V$ with $\langle W\rangle_{\mathbb F_{q^n}}=\mathbb V$ and $W\cap\Gamma=\{0\}$.
--   3. A field automorphism $\sigma$ of $\mathbb F_{q^n}$ and a non-degenerate reflexive sesquilinear form $\beta:\mathbb V\times\mathbb V\to\mathbb F_{q^n}$ with companion automorphism $\sigma$ (linear in the first argument, $\beta(v,aw)=a^\sigma\beta(v,w)$ in the second), which takes values in $\mathbb F_q$ on $W\times W$. Thus $\beta$ is the extension to $\mathbb V$ of the form $\beta'=\beta|_{W\times W}:W\times W\to\mathbb F_q$.
--
--   From these data the following objects are built.
--
--   - The orthogonal complement of an $\mathbb F_{q^n}$-subspace $S$ of $\mathbb V$: $S^\perp=\{v\in\mathbb V:\beta(v,s)=0 \text{ for all } s\in S\}$.
--   - The orthogonal complement with respect to $\beta'$ of an $\mathbb F_q$-subspace $S$: $S^{\perp'}=\{w\in W:\beta'(w,s)=0\text{ for all } s\in S\}$.
--   - The $\mathbb F_q$-subspace $U=\langle W,\Gamma\rangle_{\mathbb F_q}\cap\Lambda$ of $\Lambda$.
--   - The **Delsarte dual** of $U$ (Definition 3.2): the $\mathbb F_q$-subspace
--
--   $$
--   \bar U = W+\Gamma^\perp \;=\;\{\,w+\Gamma^\perp : w\in W\,\}\ \subseteq\ \mathbb V/\Gamma^\perp .
--   $$
--
--   The paper starts from a $k$-dimensional $\mathbb F_q$-subspace $U$ of $\Lambda$ with $k>r$, takes an embedding of $\Lambda$ in $\mathbb V$ with $U=\langle W,\Gamma\rangle_{\mathbb F_q}\cap\Lambda$ (which exists by [21, Theorems 1, 2] of the paper's bibliography), and a form $\beta'$ on $W$, extended to $\beta$. Every statement of the mission quantifies over all such data, so it applies to the Delsarte dual obtained by any admissible choice.
--
--   **Formalization Note** The data form a Lean `structure DelsarteSetting F K 𝕍`; the embedding is data, not a theorem. The form is `β : 𝕍 →ₗ[K] 𝕍 →ₛₗ[σ] K` with `σ : K ≃+* K`; non-degeneracy is one-sided ($\beta(v,\cdot)=0\Rightarrow v=0$), which suffices for a reflexive form. The paper's $\beta'$ is recovered as the restriction of $\beta$ to $W$: it is $\mathbb F_q$-valued, $\mathbb F_q$-sesquilinear with companion $\sigma|_{\mathbb F_q}$, reflexive, and non-degenerate because $W$ spans $\mathbb V$; conversely every such $\beta'$ extends to such a $\beta$ (p. 8). `U` is an `F`-submodule of the subtype `↥Λ`, so that "h-scattered in $\Lambda$" is Definition 1.1 with $V:=\Lambda$. `dual` is the image of $W$ under the quotient map $\mathbb V\to\mathbb V/\Gamma^\perp$.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, pp. 8–9, §3 (setting) and Definition 3.2

import Mathlib

namespace HScattered.Delsarte

/-- The setting of §3 (Csajbók–Marino–Polverino–Zullo, arXiv:1906.10590v2, pp. 8–9).
`F = 𝔽_q`, `K = 𝔽_{qⁿ}`, and `𝕍 = V(k, qⁿ)` with `k = finrank K 𝕍`.

* `Λ ⊕ Γ = 𝕍` (the embedding of `Λ = V(r, qⁿ)` in `𝕍` of [21, Theorems 1, 2], taken as data);
* `W` is a `k`-dimensional `𝔽_q`-subspace of `𝕍` with `⟨W⟩_{𝔽_{qⁿ}} = 𝕍` and `W ∩ Γ = {0}`;
* `β : 𝕍 × 𝕍 → 𝔽_{qⁿ}` is a non-degenerate reflexive sesquilinear form with companion
  automorphism `σ` (linear in the first argument, `σ`-semilinear in the second) which takes
  `𝔽_q`-values on `W × W`, i.e. `β` is the extension to `𝕍` of a form `β' : W × W → 𝔽_q`. -/
structure DelsarteSetting (F K 𝕍 : Type*) [Field F] [Field K] [Algebra F K]
    [AddCommGroup 𝕍] [Module K 𝕍] [Module F 𝕍] [IsScalarTower F K 𝕍] where
  /-- `Λ = V(r, qⁿ)`, the space containing `U`. -/
  Λ : Submodule K 𝕍
  /-- The complement `Γ`, with `𝕍 = Λ ⊕ Γ`. -/
  Γ : Submodule K 𝕍
  isCompl_Λ_Γ : IsCompl Λ Γ
  /-- The `k`-dimensional `𝔽_q`-subspace `W` of `𝕍`. -/
  W : Submodule F 𝕍
  finrank_W : Module.finrank F W = Module.finrank K 𝕍
  span_W : Submodule.span K (W : Set 𝕍) = ⊤
  W_inf_Γ : W ⊓ Γ.restrictScalars F = ⊥
  /-- The companion automorphism `σ` of `𝔽_{qⁿ}`. -/
  σ : K ≃+* K
  /-- The sesquilinear form `β`: `K`-linear in the first argument, `σ`-semilinear in the second. -/
  β : 𝕍 →ₗ[K] 𝕍 →ₛₗ[(σ : K →+* K)] K
  nondegenerate : ∀ v : 𝕍, (∀ w : 𝕍, β v w = 0) → v = 0
  reflexive : ∀ v w : 𝕍, β v w = 0 → β w v = 0
  /-- `β` restricts to an `𝔽_q`-valued form `β'` on `W × W`. -/
  mem_range_algebraMap : ∀ w₁ ∈ W, ∀ w₂ ∈ W, β w₁ w₂ ∈ Set.range (algebraMap F K)

namespace DelsarteSetting

variable {F K 𝕍 : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup 𝕍] [Module K 𝕍] [Module F 𝕍] [IsScalarTower F K 𝕍]

/-- The orthogonal complement `S^⊥ = {v ∈ 𝕍 : β(v, s) = 0 for all s ∈ S}` of a
`𝔽_{qⁿ}`-subspace `S` of `𝕍` with respect to `β`. -/
def orth (D : DelsarteSetting F K 𝕍) (S : Submodule K 𝕍) : Submodule K 𝕍 :=
  ⨅ s : S, LinearMap.ker (D.β.flip (s : 𝕍))

/-- The orthogonal complement `S^{⊥′} = {w ∈ W : β′(w, s) = 0 for all s ∈ S}` with respect to
the restricted form `β′ = β|_{W × W}`, as an `𝔽_q`-subspace of `W` (sitting in `𝕍`). -/
def orthW (D : DelsarteSetting F K 𝕍) (S : Submodule F 𝕍) : Submodule F 𝕍 :=
  D.W ⊓ ⨅ s : S, LinearMap.ker ((D.β.flip (s : 𝕍)).restrictScalars F)

/-- `U = ⟨W, Γ⟩_{𝔽_q} ∩ Λ`, as an `𝔽_q`-subspace of `Λ`. -/
def U (D : DelsarteSetting F K 𝕍) : Submodule F D.Λ :=
  (D.W ⊔ D.Γ.restrictScalars F).comap (D.Λ.subtype.restrictScalars F)

/-- Definition 3.2: the Delsarte dual `Ū = W + Γ^⊥` of `U`, an `𝔽_q`-subspace of `𝕍 / Γ^⊥`. -/
def dual (D : DelsarteSetting F K 𝕍) : Submodule F (𝕍 ⧸ D.orth D.Γ) :=
  D.W.map ((D.orth D.Γ).mkQ.restrictScalars F)

end DelsarteSetting

end HScattered.Delsarte


