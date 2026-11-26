-- Prove2me | Definitions.Def_StreamSubmod_Supplement_Algorithm3
-- name    : StreamSubmod_Supplement_Algorithm3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:43:21.743038+00:00
-- url     : https://prove2.me/theorems/1719450d-9136-47d9-ac66-0987cf564eed
-- title:
--   Algorithm 3: StreamProcessExtension (simplified) $(p,c)$
-- statement:
--   Algorithm 3 has parameters $p\in(0,1)$ and $c>0$ and an estimate $\tau$ of $f(\mathrm{OPT})$. It maintains a fractional solution $x$, initially $\mathbf 1_\varnothing$. When an element $e$ arrives,
--
--   $$
--   \text{if }\ \partial_eF(x)\ge\frac{c\tau}{k}\ \text{ then }\ x\leftarrow x+\min\{p,\,k-\|x\|_1\}\cdot\mathbf 1_e .
--   $$
--
--   Let $\hat x$ be the final value of $x$. The algorithm then rounds $\hat x$ to a feasible set $S_1$ (line 4), runs OfflineAlg with $\operatorname{supp}(\hat x)$ as the ground set to obtain $S_2$ (line 5), and returns the better of $S_1$ and $S_2$ (line 6). The module defines:
--
--   1. one iteration of the loop (line 3);
--   2. the fractional solution after a list of arriving elements (lines 1–3), whose value on the whole stream is $\hat x$;
--   3. the output for given seeds of the rounding and of OfflineAlg (lines 4–6).
--
--   This is the multilinear-extension variant of the paper's streaming algorithm, analysed in Appendix C.
--
--   **Formalization Note** The stream is a list and the loop is a left fold over it. The returned set is $S_2$ if $f(S_2)>f(S_1)$ and $S_1$ otherwise, so its value is $\max\{f(S_1),f(S_2)\}$.
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Algorithm 3, p.22

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_StreamSubmod_postProcess
import Definitions.Def_StreamSubmod_Supplement_Basic

namespace StreamSubmod.Supplement

open NonmonotoneSubmod.Shared

variable {E : Type} [Fintype E] [DecidableEq E]

/-- One iteration of the loop of Algorithm 3, StreamProcessExtension (simplified) `(p, c)`
(Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, Algorithm 3, line 3, p.22): when the
element `e` arrives at the fractional solution `x`,
"if `∂_eF(x) ≥ cτ/k` then `x ← x + min{p, k − ‖x‖₁} · 𝟏_e`". -/
noncomputable def alg3Step (f : Finset E → ℝ) (k : ℕ) (p c τ : ℝ) (x : E → ℝ) (e : E) :
    E → ℝ :=
  if c * τ / (k : ℝ) ≤ partialDeriv f x e then
    fun i => x i + min p ((k : ℝ) - l1 x) * ind {e} i
  else x

/-- The fractional solution `x` of Algorithm 3 after the elements of the list `L` have arrived, in
order (Algorithm 3, lines 1–3, p.22), starting from `x = 𝟏_∅`. For the whole stream `σ`,
`alg3Run f k p c τ σ` is the vector `x̂` of the paper ("the final value of the fractional solution
`x`", p.22). -/
noncomputable def alg3Run (f : Finset E → ℝ) (k : ℕ) (p c τ : ℝ) (L : List E) : E → ℝ :=
  L.foldl (alg3Step f k p c τ) (fun _ => 0)

/-- The output of Algorithm 3 on the stream `σ` (Algorithm 3, lines 4–6, p.22), when the rounding
`R` uses the seed `ω'` and the offline algorithm `Off` uses the seed `ω`: `S₁ = R ω' x̂` (line 4),
`S₂ = Off ω (supp x̂)` (line 5, OfflineAlg run with `supp(x̂)` as the ground set), and the better of
the two (line 6).

**Formalization Note.** `better f S₁ S₂` (published with `StreamSubmod.postProcess`) returns `S₂`
if `f(S₂) > f(S₁)` and `S₁` otherwise; either way its value is `max{f(S₁), f(S₂)}`. -/
noncomputable def alg3Out {Ω Ω' : Type} (f : Finset E → ℝ) (k : ℕ) (p c τ : ℝ)
    (Off : Ω → Finset E → Finset E) (R : Ω' → (E → ℝ) → Finset E) (σ : List E) (ω : Ω)
    (ω' : Ω') : Finset E :=
  StreamSubmod.better f (R ω' (alg3Run f k p c τ σ)) (Off ω (supp (alg3Run f k p c τ σ)))

end StreamSubmod.Supplement


