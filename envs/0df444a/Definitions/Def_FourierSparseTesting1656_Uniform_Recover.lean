-- Prove2me | Definitions.Def_FourierSparseTesting1656_Uniform_Recover
-- name    : FourierSparseTesting1656_Uniform_Recover
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:32:20.636588+00:00
-- url     : https://prove2.me/theorems/aaf5257e-958c-47a3-b21a-7c6b97b80ca6
-- title:
--   Algorithm 2 (Recover): basis pursuit on a fixed sample list with Boolean and sparsity tests
-- statement:
--   Let $H\le\mathbb F_2^n$ be a subspace with a complement $W$ of $H^\perp$, let $s\ge1$, and fix a list $h_1,\dots,h_q\in H$. Recover, run on $g:H\to\{-1,+1\}$, reads only the answers $y_i=g(h_i)$. If the list contains every point of $H$, the candidate spectrum $\hat z$ is the exact spectrum of the queried values; otherwise $\hat z$ is a minimizer of the basis pursuit problem
--   $$\hat z\in\arg\min_{z\in\mathbb R^{W}}\sum_{\gamma\in W}|z_\gamma|\quad\text{subject to}\quad\sum_{\gamma\in W}\chi_\gamma(h_i)z_\gamma=y_i\ (i=1,\dots,q),$$
--   chosen by a fixed deterministic rule. The candidate function is $\tilde g(h)=\sum_{\gamma\in W}\hat z_\gamma\chi_\gamma(h)$. Recover returns $\tilde g$ if it is Boolean on all of $H$ and $\hat z$ has at most $s$ nonzero entries, and otherwise the constant function $+1$.
--
--   This is the recovery routine whose single-list guarantee is Lemma 4.1.
--
--   **Formalization Note** The fixed tie rule is Lean's choice function on the set of minimizers. For answers read from an actual $g$ the problem is feasible; the zero vector is only a convention for infeasible answer lists, which `recover` never produces.
-- source:
--   Arijit Ghosh, Manmatha Roy, STOC 2027 submission #1656 (October 2026), pp. 16–17, §4.1, Eq. (17) and Algorithm 2 (Recover); PDF SHA256 5374116f8d05176f80f62c5fdaaddae029e1f9e6af853c5a8e1873cb4e83a123

import Mathlib
import Definitions.Def_FourierSparseTesting1656_Uniform_Basic

set_option autoImplicit false

namespace FourierSparseTesting1656.Uniform

open FourierDimTesting102.Quantum
open Classical

/-- The answer recorded for the point `h`: the answer at its first occurrence in the list
(used only when the list contains every point of `H`). -/
noncomputable def answerAt {n : ℕ} {H : Submodule (ZMod 2) (V n)} (L : List H) (ys : List Bool)
    (h : H) : Bool :=
  ys.getD (L.idxOf h) false

/-- Eq. (17), p.16: `z ∈ ℝ^W` is feasible for the list `h₁,…,h_q` and answers `y_i ∈ {±1}`
when `∑_{γ ∈ W} χ_γ(h_i) z_γ = y_i` for every `i ≤ q`. -/
def BPFeasible {n : ℕ} (H W : Submodule (ZMod 2) (V n)) (L : List H) (ys : List Bool) (z : W → ℝ) :
    Prop :=
  ∀ i : Fin L.length, ∑ γ : W, chi (γ : V n) ((L.get i : H) : V n) * z γ = signOf (ys.getD i false)

/-- The `ℓ₁` norm `∑_γ |z_γ|` of a coefficient vector on `W`. -/
noncomputable def l1 {n : ℕ} (W : Submodule (ZMod 2) (V n)) (z : W → ℝ) : ℝ := ∑ γ : W, |z γ|

/-- Eq. (17), p.16: the set of basis-pursuit minimizers, `argmin ‖z‖₁` subject to `Az = y`. -/
def BPMinimizers {n : ℕ} (H W : Submodule (ZMod 2) (V n)) (L : List H) (ys : List Bool) :
    Set (W → ℝ) :=
  {z | BPFeasible H W L ys z ∧ ∀ z', BPFeasible H W L ys z' → l1 W z ≤ l1 W z'}

/-- Algorithm 2, step 2, p.17: the candidate spectrum `ẑ`. When the list contains every point
of `H`, it is the exact spectrum of the queried values; otherwise it is a basis-pursuit
minimizer chosen by the fixed choice rule. (For answers read from an actual `g` the problem is
feasible; the value `0` is only a convention for infeasible answer lists, which never arise.) -/
noncomputable def candidateSpectrum {n : ℕ} (H W : Submodule (ZMod 2) (V n)) (L : List H)
    (ys : List Bool) : W → ℝ :=
  if ∀ h : H, h ∈ L then subCoeff H W (fun h => signOf (answerAt L ys h))
  else if hne : (BPMinimizers H W L ys).Nonempty then hne.some else 0

/-- Algorithm 2, step 3: the function `g̃(h) = ∑_{γ ∈ W} ẑ_γ χ_γ(h)` on `H` with spectrum `ẑ`. -/
noncomputable def candidateFun {n : ℕ} (H W : Submodule (ZMod 2) (V n)) (L : List H) (ys : List Bool)
    (h : H) : ℝ :=
  ∑ γ : W, candidateSpectrum H W L ys γ * chi (γ : V n) (h : V n)

/-- Algorithm 2, step 3: the candidate passes when `g̃` is Boolean (`±1`-valued everywhere on
`H`) and `ẑ` has at most `s` nonzero entries. -/
def candidatePasses {n : ℕ} (s : ℕ) (H W : Submodule (ZMod 2) (V n)) (L : List H) (ys : List Bool) :
    Prop :=
  (∀ h : H, candidateFun H W L ys h = 1 ∨ candidateFun H W L ys h = -1) ∧
    (Finset.univ.filter fun γ : W => candidateSpectrum H W L ys γ ≠ 0).card ≤ s

/-- Algorithm 2 (`Recover`), p.17, as a function of the list and the answers only: return `g̃`
(bit `true` encodes the value `-1`) if it passes, and otherwise the constant `+1` function. -/
noncomputable def recoverFromAnswers {n : ℕ} (s : ℕ) (H W : Submodule (ZMod 2) (V n)) (L : List H)
    (ys : List Bool) : H → Bool :=
  if candidatePasses s H W L ys then fun h => decide (candidateFun H W L ys h = -1)
  else fun _ => false

/-- Algorithm 2 run on `g : H → {±1}` (bit encoded): it queries exactly `g(h₁),…,g(h_q)`. -/
noncomputable def recover {n : ℕ} (s : ℕ) (H W : Submodule (ZMod 2) (V n)) (L : List H) (g : H → Bool) :
    H → Bool :=
  recoverFromAnswers s H W L (L.map g)

end FourierSparseTesting1656.Uniform


