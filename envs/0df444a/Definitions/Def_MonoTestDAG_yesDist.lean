-- Prove2me | Definitions.Def_MonoTestDAG_yesDist
-- name    : MonoTestDAG_yesDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:46.293508+00:00
-- url     : https://prove2.me/theorems/57c9a488-7aac-481b-9d08-f32378ce1e9f
-- title:
--   The YES and NO distributions of §4.3
-- statement:
--   Fix a bipartite graph $U=(L,R;E)$, a matching $M=M_i$ and a weight function $w=w_i$ certifying that it is positive. Put $\delta:=\min_{(\ell,r)\in M}(w(\ell)+w(r))$ and $\tilde w:=w/\delta-1/4$. Put $f(\ell):=\tilde w(\ell)$ on $L$, $f(r):=-\tilde w(r)$ on $R$, and $\Delta_e:=f(\ell)-f(r)$ for $e=(\ell,r)\in M$. The function $g$ equals $f$ except that $g(\ell)=f(\ell)-\Delta_e/2$ and $g(r)=f(r)+\Delta_e/2$ for $e=(\ell,r)\in M$.
--
--   Let $h:=1/8$, and let $Z_e\sim\mathrm{Unif}\{0,1,2,3\}$ be independent over $e\in M$, with $\eta_e:=hZ_e$ and $\eta'_e:=h\cdot((Z_e-1)\bmod 4)$. For $e=(\ell,r)\in M$,
--   $$
--   F^+(\ell)=g(\ell)+\eta_e,\quad F^+(r)=g(r)+\eta_e,\qquad F^-(\ell)=g(\ell)+\eta_e,\quad F^-(r)=g(r)+\eta'_e,
--   $$
--   and $F^\pm=g$ at unmatched vertices. $D^\pm_i$ is the law of $F^\pm$, and $D^\pm$ samples $I\sim\mathrm{Unif}([s])$ and then a function from $D^\pm_I$.
--
--   **Formalization Note.** The noise vector is $Z:M\to\mathrm{Fin}\,4$, and $(Z_e-1)\bmod4$ is subtraction in `Fin 4`. The shift and noise at a vertex are sums over the matching edges at that vertex; a matching has at most one, and the sum is $0$ at an unmatched vertex. For an empty $M$ the definition uses $\delta:=1$, a case the paper never reaches since $|M_i|\ge4\varepsilon n_0>0$. The module also defines `margin`, `normWeight`, `baseF`, `gapAt`, `slackG`, `noiseStep`, `yesFn`, `noFn`, `noiseLaw`, `noiseCount`, `condYes`, `condNo` and `noDist`.
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), §4.3.1–4.3.2, pp.17–19

import Mathlib

/-!
# The YES/NO distributions of §4.3

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), §4.3.1–4.3.2, pp.17–19.

Fix a bipartite graph `U = (L, R; E)`, a matching `M = M_i ⊆ E` and a weight function
`w = w_i : L ∪ R → ℝ` certifying that `M` is positive. Then
* `δ := min_{(ℓ,r) ∈ M} (w(ℓ) + w(r))` and `w̃ := w/δ − 1/4` (so (4) holds);
* `f(ℓ) := w̃(ℓ)` on `L`, `f(r) := −w̃(r)` on `R`, and `Δ_e := f(ℓ) − f(r)` for `e = (ℓ, r) ∈ M`;
* `g := f` shifted by `−Δ_e/2` at a matched `ℓ` and by `+Δ_e/2` at a matched `r` (display (5));
* with `h := 1/8` and independent `Z_e ∼ Unif{0,1,2,3}`, `η_e := h Z_e`, the YES function adds
  `η_e` at both endpoints of `e ∈ M`; the NO function adds `η_e` at `ℓ` and
  `η'_e := h·((Z_e − 1) mod 4)` at `r`;
* `D^±_i` is the law of these functions; `D^±` samples `I ∼ Unif([s])` and then `D^±_I`.

**Formalization Note.** The noise vector is `Z : M → Fin 4`, uniform; `(Z_e − 1) mod 4` is the
subtraction of `Fin 4`. The shift and the noise at a vertex are sums over the matching edges at
that vertex: since `M` is a matching there is at most one such edge, and the sum is `0` at an
unmatched vertex. The paper's `δ_i` is a minimum over the nonempty `M_i`; for an empty `M` the
definition uses `δ := 1` (never used by the paper, where `|M_i| ≥ 4ε n₀ > 0`).
-/

namespace MonoTestDAG

variable {L R : Type} [DecidableEq L] [DecidableEq R]

/-- `δ_i := min_{e = (ℓ, r) ∈ M_i} (w_i(ℓ) + w_i(r))` (p.17). -/
noncomputable def margin (M : Finset (L × R)) (w : L ⊕ R → ℝ) : ℝ :=
  if h : M.Nonempty then M.inf' h (fun e => w (.inl e.1) + w (.inr e.2)) else 1

/-- The normalized weight `w̃_i(v) := w_i(v)/δ_i − 1/4` (p.18). -/
noncomputable def normWeight (M : Finset (L × R)) (w : L ⊕ R → ℝ) (v : L ⊕ R) : ℝ :=
  w v / margin M w - 1 / 4

/-- `f_i(ℓ) = w̃_i(ℓ)` for `ℓ ∈ L` and `f_i(r) = −w̃_i(r)` for `r ∈ R` (p.18). -/
noncomputable def baseF (M : Finset (L × R)) (w : L ⊕ R → ℝ) : L ⊕ R → ℝ
  | .inl l => normWeight M w (.inl l)
  | .inr r => - normWeight M w (.inr r)

/-- `Δ_e := f_i(ℓ) − f_i(r)` for `e = (ℓ, r)` (p.18). -/
noncomputable def gapAt (M : Finset (L × R)) (w : L ⊕ R → ℝ) (e : L × R) : ℝ :=
  baseF M w (.inl e.1) - baseF M w (.inr e.2)

/-- The monotone function with slack `g_i` of display (5), p.18. -/
noncomputable def slackG (M : Finset (L × R)) (w : L ⊕ R → ℝ) : L ⊕ R → ℝ
  | .inl l => baseF M w (.inl l) - (∑ e ∈ M.filter (fun e => e.1 = l), gapAt M w e) / 2
  | .inr r => baseF M w (.inr r) + (∑ e ∈ M.filter (fun e => e.2 = r), gapAt M w e) / 2

/-- The step size `h := 1/8` (p.18). -/
noncomputable def noiseStep : ℝ := 1 / 8

/-- The YES function `F⁺_i` for the noise vector `Z = (Z_e)_{e ∈ M_i}` (p.18). -/
noncomputable def yesFn (M : Finset (L × R)) (w : L ⊕ R → ℝ) (Z : ↥M → Fin 4) : L ⊕ R → ℝ
  | .inl l => slackG M w (.inl l) +
      noiseStep * ∑ e ∈ (Finset.univ : Finset ↥M).filter (fun e => e.1.1 = l), ((Z e : ℕ) : ℝ)
  | .inr r => slackG M w (.inr r) +
      noiseStep * ∑ e ∈ (Finset.univ : Finset ↥M).filter (fun e => e.1.2 = r), ((Z e : ℕ) : ℝ)

/-- The NO function `F⁻_i` for the noise vector `Z`: the right endpoint of `e` receives
`h·((Z_e − 1) mod 4)` (pp.18–19). -/
noncomputable def noFn (M : Finset (L × R)) (w : L ⊕ R → ℝ) (Z : ↥M → Fin 4) : L ⊕ R → ℝ
  | .inl l => slackG M w (.inl l) +
      noiseStep * ∑ e ∈ (Finset.univ : Finset ↥M).filter (fun e => e.1.1 = l), ((Z e : ℕ) : ℝ)
  | .inr r => slackG M w (.inr r) +
      noiseStep * ∑ e ∈ (Finset.univ : Finset ↥M).filter (fun e => e.1.2 = r),
        (((Z e - 1 : Fin 4) : ℕ) : ℝ)

/-- The law of the noise: `Z_e ∼ Unif{0, 1, 2, 3}` independently over `e ∈ M_i`. -/
noncomputable def noiseLaw (M : Finset (L × R)) : PMF (↥M → Fin 4) :=
  PMF.uniformOfFintype (↥M → Fin 4)

/-- `X_i := |{e ∈ M_i : Z_e ≠ 0}|` (Lemma 4.5, p.19). -/
noncomputable def noiseCount (M : Finset (L × R)) (Z : ↥M → Fin 4) : ℕ :=
  (Finset.univ.filter (fun e => Z e ≠ 0)).card

/-- The conditional YES distribution `D⁺_i`, the law of `F⁺_i` (p.18). -/
noncomputable def condYes (M : Finset (L × R)) (w : L ⊕ R → ℝ) : PMF (L ⊕ R → ℝ) :=
  (noiseLaw M).map (yesFn M w)

/-- The conditional NO distribution `D⁻_i`, the law of `F⁻_i` (p.19). -/
noncomputable def condNo (M : Finset (L × R)) (w : L ⊕ R → ℝ) : PMF (L ⊕ R → ℝ) :=
  (noiseLaw M).map (noFn M w)

/-- The YES distribution `D⁺`: sample `I ∼ Unif([s])`, then `F ∼ D⁺_I` (p.19). -/
noncomputable def yesDist {s : ℕ} [NeZero s] (M : Fin s → Finset (L × R))
    (w : Fin s → L ⊕ R → ℝ) : PMF (L ⊕ R → ℝ) :=
  (PMF.uniformOfFintype (Fin s)).bind (fun i => condYes (M i) (w i))

/-- The NO distribution `D⁻`: sample `I ∼ Unif([s])`, then `F ∼ D⁻_I` (p.19). -/
noncomputable def noDist {s : ℕ} [NeZero s] (M : Fin s → Finset (L × R))
    (w : Fin s → L ⊕ R → ℝ) : PMF (L ⊕ R → ℝ) :=
  (PMF.uniformOfFintype (Fin s)).bind (fun i => condNo (M i) (w i))

end MonoTestDAG


