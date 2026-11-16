-- Prove2me | Definitions.Def_CondGeoVerif_Supplement_boolComp
-- name    : CondGeoVerif_Supplement_boolComp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:09:22.783728+00:00
-- url     : https://prove2.me/theorems/6f90647c-e8d3-4f15-bf4b-74a7d22d1236
-- title:
--   Sign rules, Boolean compositions $b(\mathrm{sign}(W^\top x))$, essential rules, signed relabelings, and the classes $\mathcal C_{K,d}$, $\mathcal H_d$, $Q_{t,d}$, $S_{t,d}$
-- statement:
--   Labels and signs take values in $\{-1,1\}$; $\mathrm{sign}(0)=+1$. For a Boolean rule $b:\{-1,1\}^k\to\{-1,1\}$ put $f(u)=b(\mathrm{sign}\,u_1,\dots,\mathrm{sign}\,u_k)$, so that $\mathcal H_{b,d}=\{x\mapsto f(W^\top x):W^\top W=I_k\}$ is the projection class of $f$.
--
--   1. $b$ is **essential** if each coordinate is pivotal for some assignment of the others.
--   2. A **signed permutation matrix** has one entry $\pm1$ in each row and column; the **symmetry group** $S_b$ consists of those $Q$ with $f(Q^\top u)=f(u)$ for almost every $u$ under $N(0,I_k)$, and $r_b(V,W)=\min_{Q\in S_b}\|W-VQ\|_F$.
--   3. A **signed relabeling** of the columns of $W\in\mathbb R^{d\times \ell}$ along a bijection $e:[k]\to[\ell]$ replaces column $i$ by $\pm W_{\cdot,e(i)}$.
--   4. The Gaussian disagreement of two predictors is $P(h(X)\ne h'(X))$, $X\sim N(0,I_d)$; $A_K=8K\cdot4^K$ and $\gamma_K=2^{-3K}/(32K^2)$ as in (C.1).
--   5. $\mathcal C_{K,d}$ is the class of all predictors $x\mapsto b(\mathrm{sign}(W^\top x))$ with an arbitrary Boolean rule $b$ of rank $\ell\le\min(K,d)$ and an orthonormal frame $W\in\mathbb R^{d\times\ell}$, constants included ($\ell=0$).
--   6. Homogeneous halfspaces $\mathcal H_d=\{x\mapsto\mathrm{sign}\langle v,x\rangle:\|v\|=1\}$; parity classes $Q_{t,d}=\{x\mapsto f_t(v\cdot x,w\cdot x):\|v\|=\|w\|=1,\ v\perp w\}$ with $f_t(s,u)=\mathrm{sign}(s)\,\mathrm{sign}(u-t)$; centered slabs $S_{t,d}=\{x\mapsto 2\cdot1\{|w\cdot x|\le t\}-1:\|w\|=1\}$.
--
--   The module also fixes the message type of Theorem C.7 (a rank $\ell\le K$, a truth table and a $d\times\ell$ matrix), the property that a verifier outputs exactly the composition its message names with an orthonormal frame, and properness with respect to an arbitrary class.
--
--   **Formalization Note** Labels are Booleans with `true` for $+1$. All classes are projection classes `projClass` of the live mission, with frames from the published Stiefel set.
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §4, p.8 (PDF p.11); App. C, pp.28–29, (C.1) (PDF pp.31–32); §C.7, p.36; §4.2–4.3, pp.9–10; (E.1), p.43; App. F, p.47

import Mathlib
import Definitions.Def_CondGeoVerif_OneMsgVerifier

set_option autoImplicit false

namespace CondGeoVerif.Supplement

noncomputable section

open MeasureTheory ProjLikeRetr.Stiefel CondGeoVerif
open scoped Matrix

/-- The sign of a real number as a label: `true` (`+1`) iff `0 ≤ s` (Chen, *The Conditional
Geometry of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, App. C, p.28 =
PDF p.31: "a sign on a zero hyperplane can be chosen arbitrarily"). -/
def sgn (s : ℝ) : Bool := decide (0 ≤ s)

/-- The same sign as a real number in `{−1, 1}`: `1` iff `0 ≤ s`. -/
noncomputable def sgnR (s : ℝ) : ℝ := if 0 ≤ s then 1 else -1

/-- The coordinatewise sign vector `(sign u₁, …, sign u_k) ∈ {−1, 1}ᵏ`. -/
def signs {k : ℕ} (u : Vec k) : Fin k → Bool := fun i => sgn (u i)

/-- **Boolean compositions of orthogonal halfspaces** (Chen, Oct. 2026, App. C, p.28 = PDF p.31):
for a Boolean rule `b : {−1, 1}ᵏ → {−1, 1}`, `f(u) = b(sign u₁, …, sign u_k)`; then
`H_{b,d} = {x ↦ f(Wᵀx) : WᵀW = I_k}` is `projClass {boolComp b} d`.

**Formalization Note** Labels and signs are `Bool` (`true` ↔ `+1`); the sign of `0` is `+1`. Every
statement of the supplement involving signs concerns probabilities under laws with Gaussian (or
absolutely continuous) features, for which hyperplanes are null, so the convention at `0` is
immaterial, as the paper says. -/
def boolComp {k : ℕ} (b : (Fin k → Bool) → Bool) : Vec k → Bool := fun u => b (signs u)

/-- `b` is **essential**: each coordinate is pivotal for some assignment of the others (Chen,
Oct. 2026, App. C, p.28: "meaning each coordinate is pivotal for some assignment of the others"). -/
def IsEssential {k : ℕ} (b : (Fin k → Bool) → Bool) : Prop :=
  ∀ i : Fin k, ∃ σ : Fin k → Bool, b (Function.update σ i (!σ i)) ≠ b σ

/-- The signed permutation matrix `Q` with `Q_{j i} = ±1` if `j = e(i)` (sign `−1` iff `s i`) and
`0` otherwise, so that `(WQ)_{·, i} = ±W_{·, e(i)}`. -/
def signedPermMat {k : ℕ} (e : Equiv.Perm (Fin k)) (s : Fin k → Bool) : Matrix (Fin k) (Fin k) ℝ :=
  fun j i => if j = e i then (if s i then -1 else 1) else 0

/-- The symmetry group `S_b` (Chen, Oct. 2026, §C.1, p.28 = PDF p.31): signed permutation matrices
`Q` with `f(Qᵀu) = f(u)` for almost every `u` under `N(0, I_k)`, where `f = boolComp b`. The
quotient distance is `r_b(V, W) = min_{Q ∈ S_b} ‖W − VQ‖_F`. -/
def symGroup {k : ℕ} (b : (Fin k → Bool) → Bool) : Set (Matrix (Fin k) (Fin k) ℝ) :=
  {Q | (∃ (e : Equiv.Perm (Fin k)) (s : Fin k → Bool), Q = signedPermMat e s) ∧
    ∀ᵐ u ∂(gauss k), boolComp b (matVec Qᵀ u) = boolComp b u}

/-- A **signed relabeling** of the columns of `W ∈ ℝ^{d×ℓ}` along a bijection `e : [k] → [ℓ]`:
column `i` of the result is `−W_{·, e(i)}` if `s i` and `W_{·, e(i)}` otherwise (Chen, Oct. 2026,
Theorem C.3, p.29 = PDF p.32). -/
def relabel {d k ℓ : ℕ} (W : Matrix (Fin d) (Fin ℓ) ℝ) (e : Fin k ≃ Fin ℓ) (s : Fin k → Bool) :
    Matrix (Fin d) (Fin k) ℝ :=
  fun r i => (if s i then -1 else 1) * W r (e i)

/-- The Gaussian disagreement `P(h(X) ≠ h'(X))`, `X ∼ N(0, I_d)`, of two predictors. -/
noncomputable def disagree {d : ℕ} (h h' : Vec d → Bool) : ℝ :=
  (gauss d {x | h x ≠ h' x}).toReal

/-- The constant `A_K = 8K·4^K` of (C.1) (Chen, Oct. 2026, p.29 = PDF p.32). -/
noncomputable def AK (K : ℕ) : ℝ := 8 * K * 4 ^ K

/-- The orbit gap `γ_K = 2^{−3K}/(32K²) = 2^{−K}/(4K A_K)` of (C.1) (Chen, Oct. 2026, p.29). -/
noncomputable def gammaK (K : ℕ) : ℝ := (2 : ℝ) ^ (-(3 * (K : ℤ))) / (32 * (K : ℝ) ^ 2)

/-- **The unknown Boolean composition class** `C_{K,d}` (Chen, Oct. 2026, §4, p.8 = PDF p.11): all
predictors `x ↦ b(sign(Wᵀx))` with an arbitrary Boolean rule `b : {−1, 1}^ℓ → {−1, 1}` and an
orthonormal frame `W ∈ ℝ^{d×ℓ}` of rank `ℓ ≤ min(K, d)`, including the constants (`ℓ = 0`). -/
def boolClass (K d : ℕ) : Set (Vec d → Bool) :=
  {h | ∃ ℓ : ℕ, ℓ ≤ K ∧ ℓ ≤ d ∧ ∃ b : (Fin ℓ → Bool) → Bool, ∃ W ∈ stiefel d ℓ,
    h = frameRule (boolComp b) W}

/-- Messages carrying a Boolean truth table of rank `ℓ ≤ K` and a `d × ℓ` frame (Chen, Oct. 2026,
Theorem C.7, p.33: "Both the Boolean table and the orthonormal frame are unknown and supplied in the
message"). -/
def BoolFrameMsg (K d : ℕ) : Type :=
  Σ ℓ : Fin (K + 1), ((Fin ℓ → Bool) → Bool) × Matrix (Fin d) (Fin ℓ) ℝ

/-- The verifier **outputs the composition named by the message**: whenever it outputs `h`, the
message's frame is orthonormal and `h = x ↦ b(sign(Wᵀx))` for the message's table `b` and frame
`W` (malformed frames are rejected). -/
def OutputsBoolFrame {K d : ℕ} (V : OneMsgVerifier d (BoolFrameMsg K d)) : Prop :=
  ∀ (msg : BoolFrameMsg K d) (s : Fin V.m → Vec d × Bool) (ω : V.Ω) (h : Vec d → Bool),
    V.decide msg s ω = some h → msg.2.2 ∈ stiefel d msg.1 ∧ h = frameRule (boolComp msg.2.1) msg.2.2

/-- A one-message verifier is **proper for a class `H`**: every output, for every message, sample
and coin value, belongs to `H` (Chen, Oct. 2026, Definition 2.1, p.3). -/
def ProperInClass {d : ℕ} {Msg : Type} (V : OneMsgVerifier d Msg) (H : Set (Vec d → Bool)) : Prop :=
  ∀ (msg : Msg) (s : Fin V.m → Vec d × Bool) (ω : V.Ω) (h : Vec d → Bool),
    V.decide msg s ω = some h → h ∈ H

/-- The rank-one sign rule `u ↦ sign(u₁)` on `ℝ¹`. -/
def halfRule : Vec 1 → Bool := fun u => sgn (u 0)

/-- **Homogeneous halfspaces** `H_d = {x ↦ sign⟨v, x⟩ : v ∈ S^{d−1}}` (Chen, Oct. 2026, App. E,
(E.1), p.43 = PDF p.46), as the projection class of `halfRule` (a unit `d × 1` frame is a unit
normal). -/
def halfspaceClass (d : ℕ) : Set (Vec d → Bool) := projClass {halfRule} d

/-- The parity rule `f_t(s, u) = sign(s)·sign(u − t)` on `ℝ²` (Chen, Oct. 2026, §4.2, p.9 = PDF
p.12; §C.7, p.36): `+1` iff the two signs agree. -/
def parityRule (t : ℝ) : Vec 2 → Bool := fun u => sgn (u 0) == sgn (u 1 - t)

/-- **The parity class** `Q_{t,d} = H_{f_t,d} = {x ↦ f_t(v·x, w·x) : ‖v‖ = ‖w‖ = 1, v ⊥ w}`
(Chen, Oct. 2026, §4.2, p.9; §C.7, p.36 = PDF p.39). -/
def parityClass (t : ℝ) (d : ℕ) : Set (Vec d → Bool) := projClass {parityRule t} d

/-- The slab rule `u ↦ 2·1{|u₁| ≤ t} − 1` on `ℝ¹`. -/
def slabRule (t : ℝ) : Vec 1 → Bool := fun u => decide (|u 0| ≤ t)

/-- **Centered slabs** `S_{t,d} = {h_w : w ∈ S^{d−1}}`, `h_w(x) = 2·1{|w·x| ≤ t} − 1` (Chen,
Oct. 2026, App. F, p.47 = PDF p.50; §4.3, p.10), as the projection class of `slabRule t`. -/
def slabClass (t : ℝ) (d : ℕ) : Set (Vec d → Bool) := projClass {slabRule t} d

end

end CondGeoVerif.Supplement


