-- Prove2me | Definitions.Def_RandTensorIso_Smoothed_Seed
-- name    : RandTensorIso_Smoothed_Seed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:37:05.392686+00:00
-- url     : https://prove2.me/theorems/d9d5ae59-a071-436e-bfbe-1c9dfd01e662
-- title:
--   Rectangles $\mathrm{Rect}_d(x;J,K)$, $(\tau,t)$-seeds (Definition 2.9), and the runs of the phase-alignment Algorithm A
-- statement:
--   For $d\in[3]$ with other modes $e<e'$, $x\in[n]$ and $J,K\subseteq[n]$, the **rectangle** $\mathrm{Rect}_d(x;J,K)$ is the set of positions $p$ with $p_d=x$, $p_e\in J$, $p_{e'}\in K$.
--
--   **Definition 2.9 (Seed).** For $S\in\mathbb C^{n\times n\times n}$, $\tau>0$ and $(i_0,j_0)\in[n]^2$ put $I_1^{(0)}=\{i_0\}$, $I_2^{(0)}=\{j_0\}$, $I_3^{(0)}=\emptyset$ and, for $t\ge0$ and every $d$ simultaneously,
--   $$I_d^{(t+1)}=I_d^{(t)}\cup\Big\{x\in[n]:\sum_{p\in\mathrm{Rect}_d(x;I_e^{(t)},I_{e'}^{(t)})}|S(p)|^2\ge\tau^2\Big\}.$$
--   $(i_0,j_0)$ is a **$(\tau,t)$-seed** of $S$ if $I_1^{(t)}=I_2^{(t)}=I_3^{(t)}=[n]$, and $S$ has a $(\tau,t)$-seed if some pair is one. The **core of $A$ has a $(\tau,t)$-seed** if some HOSVD core of $A$ does.
--
--   **Algorithm A** (Appendix A) takes $S,S'\in\mathbb Q(i)^{n\times n\times n}$, $(i_0,j_0)$, a rational $\tau>0$ and an integer $\ell\ge1$. It sets $z_1(i_0)=z_2(j_0)=1$, $I=(\{i_0\},\{j_0\},\emptyset)$, and runs five rounds: in each round, for every $d$, $N_d$ is the set of inactive $x\notin I_d$ with $\sum_{p\in\mathrm{Rect}_d(x;I_e,I_{e'})}|S(p)|^2\ge 9\tau^2/16$; for $x\in N_d$ it computes
--   $$c_x=\sum_{p\in\mathrm{Rect}_d(x;I_e,I_{e'})}S'(p)\,\overline{S(p)}\,\overline{z_e(p_e)z_{e'}(p_{e'})}$$
--   with the phases from before the round, sets $z_d(x)=1$ if $c_x=0$ and otherwise a Gaussian rational $z_d(x)$ with real and imaginary parts in $2^{-\ell-2}\mathbb Z$ and $|z_d(x)-c_x/|c_x||\le2^{-\ell}$; then $I_d\leftarrow I_d\cup N_d$ for every $d$. Afterwards it returns FAIL if some $I_d\ne[n]$, and otherwise $\tilde D_d=\operatorname{diag}(z_d(1),\dots,z_d(n))$.
--
--   **Formalization Note.** `seedActive S τ i₀ j₀ t d` is $I_d^{(t)}$ (0-based modes). The paper computes $z_d(x)$ by "Newton's iteration on $|c_x|^2$, then rounding" without fixing the rounding, so `AlgAOutputs S S' i₀ j₀ τ ℓ out` holds for the output of **every** run that makes admissible choices (`AdmissiblePhase`); `out = none` is FAIL and `out = some z` stands for $\tilde D_d=\operatorname{diag}(z_d)$. Phases of indices that are not yet active are initialised to $1$; they are never read.
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), pp. 24–25, 60 (PDF 26–27, 62), §2.3 (Rect_d), Definition 2.9, Appendix A (Algorithm A)

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_Tensor
import Definitions.Def_RandTensorIso_Smoothed_Spectral

namespace RandTensorIso.Smoothed

open Matrix
open scoped Classical

/-- The smaller of the two modes other than `d` (0-based). -/
def modeLo (d : Fin 3) : Fin 3 := if d = 0 then 1 else 0

/-- The larger of the two modes other than `d` (0-based). -/
def modeHi (d : Fin 3) : Fin 3 := if d = 2 then 1 else 2

/-- The weight `∑_{p ∈ Rect_d(x; J, K)} |S(p)|²` of the rectangle
`Rect_d(x; J, K) = {p : p_d = x, p_e ∈ J, p_{e'} ∈ K}` (`e < e'` the other two modes). -/
noncomputable def rectWeight {n : ℕ} (S : Tensor3 n) (d : Fin 3) (x : Fin n)
    (J K : Finset (Fin n)) : ℝ :=
  ∑ a ∈ J, ∑ b ∈ K, ‖S (pos d x a b)‖ ^ 2

/-- Definition 2.9: the active sets `I_d^{(t)}` of the weighted bootstrap process with threshold
`τ` started from `I^{(0)} = ({i₀}, {j₀}, ∅)`:
`I_d^{(t+1)} = I_d^{(t)} ∪ {x : ∑_{p ∈ Rect_d(x; I_e^{(t)}, I_{e'}^{(t)})} |S(p)|² ≥ τ²}`,
all three modes updated simultaneously from round `t`. -/
noncomputable def seedActive {n : ℕ} (S : Tensor3 n) (τ : ℝ) (i₀ j₀ : Fin n) :
    ℕ → Fin 3 → Finset (Fin n)
  | 0 => fun d => if d = 0 then {i₀} else if d = 1 then {j₀} else ∅
  | t + 1 => fun d =>
      seedActive S τ i₀ j₀ t d ∪
        Finset.univ.filter (fun x => τ ^ 2 ≤
          rectWeight S d x (seedActive S τ i₀ j₀ t (modeLo d)) (seedActive S τ i₀ j₀ t (modeHi d)))

/-- Definition 2.9: `(i₀, j₀)` is a `(τ, t)`-seed of `S` if `I_1^{(t)} = I_2^{(t)} = I_3^{(t)} = [n]`. -/
def IsSeed {n : ℕ} (S : Tensor3 n) (τ : ℝ) (t : ℕ) (i₀ j₀ : Fin n) : Prop :=
  ∀ d : Fin 3, seedActive S τ i₀ j₀ t d = Finset.univ

/-- Definition 2.9: `S` has a `(τ, t)`-seed. -/
def HasSeed {n : ℕ} (S : Tensor3 n) (τ : ℝ) (t : ℕ) : Prop :=
  ∃ i₀ j₀ : Fin n, IsSeed S τ t i₀ j₀

/-- The core `S_A` has a `(τ, t)`-seed (for some admissible choice of the eigenvector matrices;
under simple spectra all choices give the same moduli `|S_A(p)|`, hence the same seeds). -/
def CoreHasSeed {n : ℕ} (A : Tensor3 n) (τ : ℝ) (t : ℕ) : Prop :=
  ∃ S : Tensor3 n, IsCore A S ∧ HasSeed S τ t

/-! ### Algorithm A (Appendix A, p. 60) -/

/-- A state of Algorithm A: the active sets `I_d` and the current phases `z_d(x) ∈ ℚ(i)`. -/
abbrev AlgAState (n : ℕ) : Type := (Fin 3 → Finset (Fin n)) × (Fin 3 → Fin n → GQ)

/-- Step 1 of Algorithm A: `z₁(i₀) = z₂(j₀) = 1`, `I = ({i₀}, {j₀}, ∅)`. Phases of inactive indices
are never read; they are initialised to `1`. -/
def algAInit {n : ℕ} (i₀ j₀ : Fin n) : AlgAState n :=
  (fun d => if d = 0 then {i₀} else if d = 1 then {j₀} else ∅, fun _ _ => (1, 0))

/-- `c_x = ∑_{p ∈ Rect_d(x; I_e, I_{e'})} S'(p) · conj(S(p)) · conj(z_e(p_e) z_{e'}(p_{e'}))`. -/
noncomputable def algACoeff {n : ℕ} (S S' : GTensor n) (st : AlgAState n) (d : Fin 3)
    (x : Fin n) : ℂ :=
  ∑ a ∈ st.1 (modeLo d), ∑ b ∈ st.1 (modeHi d),
    GQ.toC (S' (pos d x a b)) * star (GQ.toC (S (pos d x a b))) *
      star (GQ.toC (st.2 (modeLo d) a) * GQ.toC (st.2 (modeHi d) b))

/-- The new indices `N_d` of a round: inactive `x ∉ I_d` whose rectangle on the active sets has
weight `∑ |S(p)|² ≥ 9τ²/16`. -/
noncomputable def algANew {n : ℕ} (S : GTensor n) (τ : ℚ) (st : AlgAState n) (d : Fin 3) :
    Finset (Fin n) :=
  Finset.univ.filter (fun x => x ∉ st.1 d ∧
    (9 * (τ : ℝ) ^ 2 / 16) ≤ rectWeight (GTensor.toC S) d x (st.1 (modeLo d)) (st.1 (modeHi d)))

/-- An admissible phase for the coefficient `c`: `1` if `c = 0`; otherwise a Gaussian rational
with real and imaginary parts in `2^{−ℓ−2} ℤ` and `|z − c/|c|| ≤ 2^{−ℓ}`. (The paper computes it by
Newton's iteration and rounding; any value with these properties is allowed.) -/
def AdmissiblePhase (ℓ : ℕ) (c : ℂ) (z : GQ) : Prop :=
  if c = 0 then z = (1, 0) else
    (z.1 * 2 ^ (ℓ + 2)).den = 1 ∧ (z.2 * 2 ^ (ℓ + 2)).den = 1 ∧
      ‖GQ.toC z - c / (‖c‖ : ℂ)‖ ≤ (2 : ℝ)⁻¹ ^ ℓ

/-- One round of Step 2 of Algorithm A: every new index `x ∈ N_d` gets an admissible phase for
`c_x` (computed with the phases from before the round), other phases are kept, and
`I_d ← I_d ∪ N_d` for every `d` simultaneously. -/
def AlgAStep {n : ℕ} (S S' : GTensor n) (τ : ℚ) (ℓ : ℕ) (st st' : AlgAState n) : Prop :=
  (∀ d, st'.1 d = st.1 d ∪ algANew S τ st d) ∧
  (∀ d x, x ∈ algANew S τ st d → AdmissiblePhase ℓ (algACoeff S S' st d x) (st'.2 d x)) ∧
  (∀ d x, x ∉ algANew S τ st d → st'.2 d x = st.2 d x)

/-- `out` is an output of some run of Algorithm A on `(S, S', (i₀, j₀), τ, ℓ)`: five rounds of
Step 2, then Step 3 (`none` = FAIL if some `I_d ≠ [n]`, otherwise `some z`, standing for
`D̃_d = diag(z_d(1), …, z_d(n))`). -/
def AlgAOutputs {n : ℕ} (S S' : GTensor n) (i₀ j₀ : Fin n) (τ : ℚ) (ℓ : ℕ)
    (out : Option (Fin 3 → Fin n → GQ)) : Prop :=
  ∃ st : Fin 6 → AlgAState n, st 0 = algAInit i₀ j₀ ∧
    (∀ t : Fin 5, AlgAStep S S' τ ℓ (st t.castSucc) (st t.succ)) ∧
    out = (if ∀ d, (st 5).1 d = Finset.univ then some (st 5).2 else none)

end RandTensorIso.Smoothed


