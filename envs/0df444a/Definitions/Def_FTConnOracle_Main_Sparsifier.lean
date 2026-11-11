-- Prove2me | Definitions.Def_FTConnOracle_Main_Sparsifier
-- name    : FTConnOracle_Main_Sparsifier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:32:35.10674+00:00
-- url     : https://prove2.me/theorems/91a4c434-9489-4966-b24e-d0b02066c6b0
-- title:
--   Cut values c_H, ε-cut sparsifiers (4.4), the parameters ε, t of (4.5), and the cut decoder (4.6)
-- statement:
--   A **weighted graph** $H$ on $[n]$ has nonnegative edge weights $w_H$; its cut value is
--
--   $$c_H(S)=\sum_{(u,v)\in\delta_H(S)} w_H(u,v).$$
--
--   For $0<\varepsilon<1$, an **$\varepsilon$-cut sparsifier** of an unweighted graph $G$ on $[n]$ is a weighted graph $H$ on $[n]$ with
--
--   $$(1-\varepsilon)\,|\delta_G(S)|\ \le\ c_H(S)\ \le\ (1+\varepsilon)\,|\delta_G(S)|\qquad\text{for every }S\subseteq[n].\qquad(4.4)$$
--
--   For an integer $f\ge1$, the construction of §4.2 sets
--
--   $$\varepsilon=\frac{1}{4f^{1/5}},\qquad t=\Big\lceil\sqrt{8\varepsilon f}\Big\rceil.\qquad(4.5)$$
--
--   Given the weights of $H$, the sketches $(b_v,s_v)$, a failure set $F$ and a cut candidate $S$, the **cut decoder** (4.6) sets $d=|\delta_F(S)|$ (the failing edges across $S$) and returns *empty* if and only if
--
--   $$\text{Test-Cut}\big(S,F,\{(b_v,s_v)\}_{v\in S},\{(b_u,b_v)\}_{\{u,v\}\in F}\big)=1\quad\text{and}\quad c_H(S)\le(1+\varepsilon)\,d.\qquad(4.6)$$
--
--   This is the per-cut decision rule of the $\tilde O(f^{2/5}n)$-bit oracle; Lemma 4.5 states its correctness.
--
--   **Formalization Note.** $H$ is a weight function `w : Sym2 (Fin n) → ℝ` (weight $0$ means no edge); `cutWeight w S` sums the weights of the pairs crossing $S$ (loops never cross). `IsCutSparsifier G w ε` includes $0<\varepsilon<1$ and $w\ge0$. `epsF f` and `tF f` are (4.5), with real powers and `Nat.ceil`. `cutDecoder f w b sk S F` returns `true` for *empty*.
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), p. 20 (PDF 22): 'Cut Sparsifiers' (4.4), 'The construction' (4.5), 'Deciding on a specific cut candidate S' (4.6)

import Mathlib
import Definitions.Def_FTConnOracle_Main_Oracle
import Definitions.Def_FTConnOracle_Main_Expander

namespace FTConnOracle.Main

/-!
# Cut sparsifiers and the cut decoder (4.6) of the `Õ(f^{2/5} n)` oracle

Parter, Tzalik, *Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space*,
STOC 2027 submission (manuscript sha256 168306b7…), p. 20 (PDF 22): (4.4), (4.5), (4.6).

* A weighted graph `H` on `[n]` with nonnegative edge weights is a weight function
  `w : Sym2 (Fin n) → ℝ`, `w ≥ 0` (weight `0` = no edge). `cutWeight w S = c_H(S)` sums the
  weights of the pairs crossing `S`.
* `epsF f = 1/(4 f^{1/5})` and `tF f = ⌈√(8 ε f)⌉` are the parameters (4.5).
* `cutDecoder` is the decision rule (4.6); it reads the sparsifier weights, the sketches and `F`.
-/

/-- `c_H(S) = ∑_{(u,v) ∈ δ_H(S)} w_H(u, v)`: the total weight of the pairs crossing `S`. -/
noncomputable def cutWeight {n : ℕ} (w : Sym2 (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ e ∈ cutEdges Finset.univ S, w e

/-- (4.4): for `0 < ε < 1`, the weighted graph `H` (nonnegative weights `w`) is an
**`ε`-cut sparsifier** of the unweighted graph `G` if
`(1 − ε)|δ_G(S)| ≤ c_H(S) ≤ (1 + ε)|δ_G(S)|` for every `S ⊆ [n]`. -/
def IsCutSparsifier {n : ℕ} (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ) (ε : ℝ) : Prop :=
  0 < ε ∧ ε < 1 ∧ (∀ e, 0 ≤ w e) ∧
    ∀ S : Finset (Fin n),
      (1 - ε) * ((delta G S).card : ℝ) ≤ cutWeight w S ∧
        cutWeight w S ≤ (1 + ε) * ((delta G S).card : ℝ)

/-- (4.5): `ε = 1/(4 f^{1/5})`. -/
noncomputable def epsF (f : ℕ) : ℝ :=
  1 / (4 * (f : ℝ) ^ ((1 : ℝ) / 5))

/-- (4.5): `t = ⌈√(8 ε f)⌉`. -/
noncomputable def tF (f : ℕ) : ℕ :=
  ⌈Real.sqrt (8 * epsF f * (f : ℝ))⌉₊

/-- The cut decoder (4.6) for a cut candidate `S`: with `d = |δ_F(S)|` (the failing edges
across `S`), it returns *empty* (`true`) if and only if
`Test-Cut(S, F, {(b_v, s_v)}_{v ∈ S}, {(b_u, b_v)}_{{u,v} ∈ F}) = 1` and `c_H(S) ≤ (1 + ε) d`,
with `ε = epsF f`. -/
noncomputable def cutDecoder {n r : ℕ} (f : ℕ) (w : Sym2 (Fin n) → ℝ) (b sk : Fin n → Fin r → ℤ)
    (S : Finset (Fin n)) (F : Finset (Sym2 (Fin n))) : Bool :=
  testCut b sk S F &&
    decide (cutWeight w S ≤ (1 + epsF f) * ((cutEdges F S).card : ℝ))

end FTConnOracle.Main


