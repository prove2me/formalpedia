-- Prove2me | Definitions.Def_HWMaskLeak_insecurity
-- name    : HWMaskLeak_insecurity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:48.4601+00:00
-- url     : https://prove2.me/theorems/859c217e-d576-44ae-871b-59fda48ff471
-- title:
--   Leakage laws $D(s)$, $D(U)$ and the insecurity $E_k(s)$, eq. (1)
-- statement:
--   Fix $k\ge1$ and a secret $s\in G=\mathbb Z/N\mathbb Z$. A **uniform $k$-party additive sharing** of $s$ chooses $X_1,\dots,X_{k-1}$ independent and uniform in $G$ and sets $X_k=s-X_1-\cdots-X_{k-1}$. The **leakage law** $D(s)$ is the distribution of $(\mathrm{wt}(X_1),\dots,\mathrm{wt}(X_k))$; for $w\in\mathbb N^k$,
--   $$
--   D(s)(w)=\frac{\#\{X\in G^k:\ X_1+\cdots+X_k=s,\ \mathrm{wt}(X_j)=w_j\ \forall j\}}{N^{k-1}}.
--   $$
--   For a uniform secret the $k$ shares are independent and uniform, so
--   $$
--   D(U)(w)=\frac{\#\{X\in G^k:\ \mathrm{wt}(X_j)=w_j\ \forall j\}}{N^{k}}.
--   $$
--   The **insecurity** of the secret $s$ is the total variation distance
--   $$
--   E_k(s):=\|D(s)-D(U)\|_{\mathrm{TV}}=\frac12\sum_{w\in W^k}\bigl|D(s)(w)-D(U)(w)\bigr|,
--   $$
--   where $W=\mathrm{wt}(G)$.
--
--   This is the quantity the mission bounds: it measures how much the Hamming weights of the $k$ shares reveal about the secret.
--
--   **Formalization Note** Uniform choices on finite sets are written as normalized counts; vectors $X\in G^k$ with coordinate sum $s$ are in bijection with the free shares $(X_1,\dots,X_{k-1})\in G^{k-1}$.
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), §1.1.1, pp.4–6, eq. (1)

import Mathlib
import Definitions.Def_HWMaskLeak_wt

namespace HWMaskLeak

/-- **The leakage law `D(s)`** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From
Additive Sharing to Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256
ab686360…), §1.1.1, pp.4–5): a uniform `k`-party additive sharing of `s ∈ G = ℤ/Nℤ` chooses
`X₁, …, X_{k−1}` independent and uniform in `G` and sets `X_k = s − X₁ − ⋯ − X_{k−1}`; `D(s)` is the law
of `(wt(X₁), …, wt(X_k))`. Its mass at `w ∈ ℕ^k` is
`#{X ∈ G^k : X₁ + ⋯ + X_k = s, wt(X_j) = w_j ∀ j} / N^{k−1}`.

**Formalization Note** The uniform choice is written as a normalized count: `(X₁, …, X_{k−1})` ranges
over `G^{k−1}`, which is in bijection with the vectors `X ∈ G^k` whose coordinates sum to `s`. -/
noncomputable def leakLaw (N : ℕ) [NeZero N] (k : ℕ) (s : ZMod N) (w : Fin k → ℕ) : ℝ :=
  ((Finset.univ.filter (fun X : Fin k → ZMod N =>
      ∑ j, X j = s ∧ ∀ j, wt N (X j) = w j)).card : ℝ) / (N : ℝ) ^ (k - 1)

/-- **The leakage law `D(U)` for a uniform secret** (same preprint, §1.1.1, p.5): when the secret is
uniform over `G`, the `k` shares are independent and uniform in `G`, so the mass of `D(U)` at
`w ∈ ℕ^k` is `#{X ∈ G^k : wt(X_j) = w_j ∀ j} / N^k`. -/
noncomputable def leakLawUnif (N : ℕ) [NeZero N] (k : ℕ) (w : Fin k → ℕ) : ℝ :=
  ((Finset.univ.filter (fun X : Fin k → ZMod N => ∀ j, wt N (X j) = w j)).card : ℝ) / (N : ℝ) ^ k

/-- **The insecurity `E_k(s)`, eq. (1)** (same preprint, §1.1.1, p.6):
`E_k(s) := ‖D(s) − D(U)‖_TV := ½ Σ_{w ∈ W^k} |D(s)(w) − D(U)(w)|`, where `W = wt(G)`.

**Formalization Note** `G = ZMod N` with `[NeZero N]`; the sum runs over `W^k`, written
`Fintype.piFinset (fun _ => weights N)`, which contains the supports of both laws. -/
noncomputable def insecurity (N : ℕ) [NeZero N] (k : ℕ) (s : ZMod N) : ℝ :=
  (1 / 2) * ∑ w ∈ Fintype.piFinset (fun _ : Fin k => weights N),
    |leakLaw N k s w - leakLawUnif N k w|

end HWMaskLeak


