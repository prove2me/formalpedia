-- Prove2me | Definitions.Def_MemoryRegret_IsL2Extractor
-- name    : MemoryRegret_IsL2Extractor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:17.962836+00:00
-- url     : https://prove2.me/theorems/ce458bbd-840f-4354-9049-4488c65b3237
-- title:
--   $(k,\ell)$-$L_2$-extractor with error $2^{-r}$ with respect to $\mu$
-- statement:
--   Let $X$ and $\iota$ be finite sets and $\mu$ a probability distribution on $X$. For functions on $\iota$ use the norms and inner product with respect to the uniform distribution on $\iota$:
--   $$\|f\|_1=\mathbb E_{i}|f(i)|,\qquad \|f\|_2=\bigl(\mathbb E_{i}f(i)^2\bigr)^{1/2},\qquad\langle f,g\rangle=\mathbb E_i[f(i)g(i)].$$
--   The matrix $M(x,i)=(-1)^{\mathrm{hyp}_i(x)}$ is a **$(k,\ell)$-$L_2$-extractor with error $2^{-r}$ with respect to $\mu$** if for every non-negative, nonzero $f:\iota\to\mathbb R$ with $\|f\|_2/\|f\|_1\le2^\ell$, the set of rows $x$ with
--   $$\frac{|\langle M_x,f\rangle|}{\|f\|_1}\ge2^{-r}$$
--   has $\mu$-mass at most $2^{-k}$.
--
--   This property says that no fairly flat distribution over hypotheses is correlated with many rows, and it is the only property of the class used by the memory lower bound.
--
--   **Formalization Note** Every $\pm1$ matrix has the form $\mathrm{sgn}(\mathrm{hyp}_i(x))$. The ratios are written multiplicatively; $f=0$ is excluded because the ratios are undefined there, and for $f\ge0$, $f\ne0$ we have $\|f\|_1>0$, so the two forms agree. The parameters $k,\ell,r$ are real numbers.
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), Definition 1, p.7; norms and inner product, §2, p.7

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec
import Definitions.Def_MemoryRegret_sgn

namespace MemoryRegret

variable {ι : Type} [Fintype ι]

/-- `‖f‖_1 = E_{h ∈_R H}[|f(h)|]`, the `ℓ_1` norm with respect to the uniform distribution
(§2, p.7). -/
noncomputable def unifNorm1 (f : ι → ℝ) : ℝ := (Fintype.card ι : ℝ)⁻¹ * ∑ i, |f i|

/-- `‖f‖_2 = (E_{h ∈_R H}[f(h)^2])^{1/2}`, the `ℓ_2` norm with respect to the uniform
distribution (§2, p.7). -/
noncomputable def unifNorm2 (f : ι → ℝ) : ℝ := Real.sqrt ((Fintype.card ι : ℝ)⁻¹ * ∑ i, f i ^ 2)

/-- `⟨f, g⟩ = E_{h ∈_R H}[f(h)·g(h)]`, the inner product with respect to the uniform
distribution (§2, p.7). -/
noncomputable def unifInner (f g : ι → ℝ) : ℝ := (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i * g i

/-- **L2-extractor with respect to µ (Definition 1).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
Definition 1, p.7: "Let X, H be two finite sets. Let µ : X → [0, 1] be a probability
distribution over X. A matrix M : X × H → {−1, 1} is a (k, ℓ)-L2-Extractor with error 2^{−r}
with respect to µ, if for every non-negative f : H → ℝ with ‖f‖_2/‖f‖_1 ≤ 2^ℓ the set of rows x
in X, with |⟨M_x, f⟩|/‖f‖_1 ≥ 2^{−r}, has probability mass at most 2^{−k} with respect to µ."

`IsL2Extractor μ hyp k ℓ r` says this for the matrix `M(x, i) = (−1)^{hyp i x}` (§2, p.7): for
every non-negative, not identically zero `f : ι → ℝ` with `‖f‖₂ ≤ 2^ℓ ‖f‖₁`, the `µ`-mass of the
rows `x` with `|⟨M_x, f⟩| ≥ 2^{−r} ‖f‖₁` is at most `2^{−k}`.

**Formalization Note.** The columns are indexed by a finite type `ι` and the matrix is given by
`hyp : ι → X → Bool` through the sign map; every `±1` matrix is of this form, and for
`ι = H` with `hyp h = h` it is the matrix of the class. Norms and the inner product are with
respect to the uniform distribution on `ι` (`unifNorm1`, `unifNorm2`, `unifInner`). The paper's
ratios are written multiplicatively; `f = 0` is excluded because the ratios `‖f‖₂/‖f‖₁` and
`|⟨M_x,f⟩|/‖f‖₁` are undefined there, and for `f ≥ 0, f ≠ 0` we have `‖f‖₁ > 0`, so the
multiplicative form is exactly the ratio form. `k, ℓ, r` are real numbers and `2^·` is
`Real.rpow`. -/
def IsL2Extractor {X : Type} [Fintype X] (μ : X → ℝ) (hyp : ι → X → Bool) (k ℓ r : ℝ) : Prop :=
  ∀ f : ι → ℝ, (∀ i, 0 ≤ f i) → (∃ i, f i ≠ 0) →
    unifNorm2 f ≤ (2 : ℝ) ^ ℓ * unifNorm1 f →
    wprob μ (fun x => (2 : ℝ) ^ (-r) * unifNorm1 f ≤ |unifInner (fun i => sgn (hyp i x)) f|)
      ≤ (2 : ℝ) ^ (-k)

end MemoryRegret


