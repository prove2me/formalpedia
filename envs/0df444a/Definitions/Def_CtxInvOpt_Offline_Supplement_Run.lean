-- Prove2me | Definitions.Def_CtxInvOpt_Offline_Supplement_Run
-- name    : CtxInvOpt_Offline_Supplement_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:07:36.545706+00:00
-- url     : https://prove2.me/theorems/9bf00a74-4d98-4a99-8ecd-9fd922f604c9
-- title:
--   Algorithm 4, pp. 22–28 — runs of ProjectedCones against an adaptive nature
-- statement:
--   This file formalizes a run of **ProjectedCones** (Algorithm 4), the paper's policy for an arbitrary initial knowledge set.
--
--   The state of the algorithm is the ordered list $\tau$ of periods whose effective differences were added to the subspace $\Delta$, its dimension $p=|\tau|$, a matrix $B_\Delta$ with $p$ orthonormal rows spanning $\Delta$, a diagonal matrix $W$ with $p-1$ entries and an orthonormal $p\times p$ matrix $U$. Write $\delta^\pi_t$ for the effective difference of period $t$: the normalized difference $f_t(x^\pi_t)-f_t(x^\star_t)$, or $0$ when this difference is $0$. Write $\Pi_\Delta\delta=B_\Delta'B_\Delta\delta$ for the orthogonal projection onto $\Delta$ and $r^\pi_t=\delta^\pi_t-\Pi_\Delta\delta^\pi_t$.
--
--   1. While $\tau$ is empty, the policy plays the proxy cost $c^\pi_t=e_1$. The first nonzero $\delta^\pi_t$ gives $\tau=(t)$, $p=1$, $B_\Delta=\delta^{\pi\prime}_t$, an empty $W$ and $U=1$.
--   2. Otherwise the policy plays $c^\pi_t=B_\Delta'U e_1$. If $\|r^\pi_t\|\le\eta$, let $v=U^{-1}B_\Delta\Pi_\Delta\delta^\pi_t$. If $v_{[2:p]}'Wv_{[2:p]}\le\epsilon^2$ the state is kept; otherwise $(W,U)$ is replaced by an output of ConeUpdate$(\Pi_\Delta\delta^\pi_t,W,U,\eta,B_\Delta,p)$.
--   3. If $\|r^\pi_t\|>\eta$, then $t$ is prepended to $\tau$, $p$ increases by one, $B_\Delta$ becomes any matrix with orthonormal rows spanning $\{\delta^\pi_i:i\in\tau\}$, $(u_1,\alpha)=$ PolyCenter$(\{\delta^\pi_i\},B_\Delta,p)$, $W=\tan^2(\alpha)I_{p-1}$, and $U$ is any orthonormal matrix with first column $u_1$.
--
--   In every period, $x^\pi_t$ is any minimizer of $f_t(x)'c^\pi_t$ over $X_t$ and $x^\star_t$ is any minimizer of $f_t(x)'c^\star$. Nature's sequences $X_t$, $f_t$ are arbitrary, so every adaptive nature and every tie-breaking rule produces a run.
--
--   **Formalization Note** Lean periods are 0-based: Lean period $t$ is the paper's period $t+1$, and the state at Lean period $t$ is the paper's state at the start of period $t+1$. The paper assumes the first difference is nonzero ($t_0=1$, p. 22); the empty-$\tau$ state covers earlier zero differences and agrees with the printed initialization when $t_0=1$. Printed slips are read as follows. Coordinates are $B_\Delta\Pi_\Delta\delta$, not $B_\Delta'\Pi_\Delta\delta$ (p. 23). $\Delta_{t+1}$ is spanned by $\tau(t+1)$, not $\tau(t)$. The stray argument in $\Pi_{\Delta_t}(\delta^\pi_t,p)$ is dropped. Algorithm 4 restarts with $W=\tan^2(\alpha)I$ from PolyCenter's $\alpha$; the prose of p. 25 and the proof on App-21 use the aperture $\arccos(\eta^{d-1}/d^{3/2})$ instead, and the definition follows Algorithm 4. The algorithm never reads $C_0$.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, pp. 22–25 (§5) and p. 28, Algorithm 4 (ProjectedCones)

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Supplement_PolyCenter

namespace CtxInvOpt.Offline.Supplement

open Matrix

/-- **Algorithm 4 (ProjectedCones), pp. 22–25 and 28.** The algorithm's state once `τ` is nonempty,
with `p = m + 1 = dim Δ`:

* `idx` lists the periods of `τ` (newest first, as in `τ(t+1) ← (t, τ(t))`);
* `B = B_Δ` has `p` orthonormal rows spanning `Δ`;
* `w` holds the `p − 1` diagonal entries of `W`;
* `U` is the orthonormal `p × p` matrix of the ellipsoidal cone `E(W, U)` in the coordinates `Bc`. -/
structure PCFrame (d : ℕ) where
  m : ℕ
  idx : Fin (m + 1) → ℕ
  B : Matrix (Fin (m + 1)) (Fin d) ℝ
  w : Fin m → ℝ
  U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ

/-- The first standard basis vector `e₁` of `ℝᵈ`. -/
def firstBasisVec (d : ℕ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i : Fin d => if (i : ℕ) = 0 then (1 : ℝ) else 0)

/-- **Algorithm 4, p. 28.** The proxy cost: `c^π = e₁` while `τ` is empty, and `c^π_t = B′_{Δ_t} U_t e₁`
otherwise. -/
noncomputable def pcProxy {d : ℕ} : Option (PCFrame d) → EuclideanSpace ℝ (Fin d)
  | none => firstBasisVec d
  | some F => WithLp.toLp 2 (F.Bᵀ *ᵥ (fun i => F.U i 0))

/-- **pp. 22–23.** The orthogonal projection `Π_Δ δ = B′Bδ` onto the row space `Δ` of a matrix `B` with
orthonormal rows. -/
def subspaceProj {d m : ℕ} (B : Matrix (Fin (m + 1)) (Fin d) ℝ)
    (δ : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (Bᵀ *ᵥ (B *ᵥ WithLp.ofLp δ))

/-- **Algorithm 4, p. 28.** One period of ProjectedCones: the state `S` at Lean period `t` and the
effective differences `δ s = δ^π_s` (zero when `f_s(x^π_s) = f_s(x⋆_s)`) determine the admissible next
states `S'`.

* **`τ` empty** (`S = none`): the period played `e₁`. If `δ^π_t = 0` the state stays empty; otherwise
  `τ = (t)`, `p = 1`, `B = δ^π_t′`, `W` is empty and `U = 1` (the printed initialization after period 1).
* **`τ` nonempty**, with `r = δ^π_t − Π_Δ δ^π_t`:
  * `‖r‖ ≤ η`: let `v = U⁻¹BΠ_Δ(δ^π_t)`. If `v′_{[2:p]} W v_{[2:p]} ≤ ε²`, keep the state; otherwise
    `(W, U) ← ConeUpdate(Π_Δ(δ^π_t), W, U, η, B, p)`, with `τ`, `Δ` and `B` unchanged.
  * `‖r‖ > η`: `τ ← (t, τ)`, `p ← p + 1`; `B` is any matrix with orthonormal rows spanning the
    `δ^π_i`, `i ∈ τ`; `(u₁, α) = PolyCenter({δ^π_i}, B, p)`; `W ← tan²(α) I_{p−1}` and `U` is any
    orthonormal matrix with first column `u₁`. -/
def IsPCStep {d : ℕ} (ε η : ℝ) (δ : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) :
    Option (PCFrame d) → Option (PCFrame d) → Prop
  | none, S' =>
      (δ t = 0 → S' = none) ∧
      (δ t ≠ 0 → S' = some ⟨0, fun _ => t, Matrix.of (fun _ j => WithLp.ofLp (δ t) j),
        Fin.elim0, 1⟩)
  | some F, S' =>
      (‖δ t - subspaceProj F.B (δ t)‖ ≤ η →
        (CtxInvOpt.Pointed.tailQuad F.w (F.Uᵀ *ᵥ (F.B *ᵥ WithLp.ofLp (subspaceProj F.B (δ t))))
            ≤ ε ^ 2 → S' = some F) ∧
        (ε ^ 2 < CtxInvOpt.Pointed.tailQuad F.w
            (F.Uᵀ *ᵥ (F.B *ᵥ WithLp.ofLp (subspaceProj F.B (δ t)))) →
          ∃ (w' : Fin F.m → ℝ) (U' : Matrix (Fin (F.m + 1)) (Fin (F.m + 1)) ℝ),
            IsConeUpdateEta η F.B F.w F.U (subspaceProj F.B (δ t)) w' U' ∧
            S' = some ⟨F.m, F.idx, F.B, w', U'⟩)) ∧
      (η < ‖δ t - subspaceProj F.B (δ t)‖ →
        ∃ (B' : Matrix (Fin (F.m + 1 + 1)) (Fin d) ℝ) (u : Fin (F.m + 1 + 1) → ℝ) (α : ℝ)
          (U' : Matrix (Fin (F.m + 1 + 1)) (Fin (F.m + 1 + 1)) ℝ),
          B' * B'ᵀ = 1 ∧
          Submodule.span ℝ (Set.range fun k => (WithLp.toLp 2 (B' k) : EuclideanSpace ℝ (Fin d))) =
            Submodule.span ℝ (Set.range fun k => δ ((Fin.cons t F.idx : Fin (F.m + 1 + 1) → ℕ) k)) ∧
          IsPolyCenter (fun k => δ ((Fin.cons t F.idx : Fin (F.m + 1 + 1) → ℕ) k)) B' u α ∧
          U' ∈ Matrix.orthogonalGroup (Fin (F.m + 1 + 1)) ℝ ∧ (∀ i, U' i 0 = u i) ∧
          S' = some ⟨F.m + 1, Fin.cons t F.idx, B', fun _ => Real.tan α ^ 2, U'⟩)

/-- **Algorithm 4 (ProjectedCones), p. 28.** `S` is a run of ProjectedCones with parameters `ε`, `η`
against the (arbitrary, adaptive) instance sequence `X, f`, true cost `cstar` and expert actions `xstar`.
Lean period `t` is the paper's period `t + 1`; `S t` is the state at the start of that period. The run
starts with `τ` empty; in every period `x^π_t ∈ ψ(c^π_t, X_t, f_t)` and `x⋆_t ∈ ψ(c⋆, X_t, f_t)` (any
minimizers), and the state moves by `IsPCStep` with the effective differences
`δ^π_s = effDiff(f_s(x^π_s) − f_s(x⋆_s))`. The algorithm does not read `C₀`. -/
def IsProjConesRun {n d : ℕ} (ε η : ℝ) (cstar : EuclideanSpace ℝ (Fin d))
    (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
    (xpi xstar : ℕ → EuclideanSpace ℝ (Fin n)) (S : ℕ → Option (PCFrame d)) : Prop :=
  S 0 = none ∧
  ∀ t, xpi t ∈ CtxInvOpt.Offline.argminSet (pcProxy (S t)) (X t) (f t) ∧
    xstar t ∈ CtxInvOpt.Offline.argminSet cstar (X t) (f t) ∧
    IsPCStep ε η (fun s => CtxInvOpt.Pointed.effDiff (f s (xpi s) - f s (xstar s))) t (S t) (S (t + 1))

end CtxInvOpt.Offline.Supplement


