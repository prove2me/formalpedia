-- Prove2me | Definitions.Def_LosslessQLTC_Heavy
-- name    : LosslessQLTC_Heavy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:17:30.488271+00:00
-- url     : https://prove2.me/theorems/6d2445ba-c03a-449a-9b22-35b25249b9a9
-- title:
--   Heavy and terminal vertices, excess, same-type excess and light squares
-- statement:
--   Fix a level $0\le r\le k-1$, a cochain with support $H_r\subseteq V_r$, and thresholds $0<\gamma_i<k-i$ for $0\le i<r$. For $x\in V_I$ and $j\notin I$, let $u_j(x)$ be the number of up-neighbours of $x$ in $H_{I\cup\{j\}}$ divided by $D_j$. For $|I|<r$,
--
--   $$H_I=\Big\{x\in V_I:\sum_{j\notin I}u_j(x)\ge\gamma_{|I|}\Big\},\qquad(4.2)$$
--
--   and $H_{r+1}=\{v\in V_{r+1}:a\lessdot v\text{ for some }a\in H_r\}$. Let $H=\bigcup_{i=0}^{r+1}H_i$ and $L=X(0)\setminus H$. For $v\in H_i$, the heavy children are $\mathrm{Ch}(v)=\{u\in H_{i-1}:u\lessdot v\}$, and $\mathrm{Ter}=\{v\in H:\mathrm{Ch}(v)=\emptyset\}$. The terminal descendants are $\mathrm{Ter}(v)=\{v\}$ for $v\in\mathrm{Ter}$ and $\mathrm{Ter}(v)=\bigcup_{u\in\mathrm{Ch}(v)}\mathrm{Ter}(u)$ otherwise. Then $H(t)=\{a\in H:t\in\mathrm{Ter}(a)\}$, $E(a)=|\mathrm{Ter}(a)|-1$ and $\|E_i\|=\sum_{a\in H_i}E(a)\|a\|$. The local charges are
--
--   $$\mathrm{Same}(a)=\sum_{|J|=i-1}(|\mathrm{Ch}(a)\cap H_J|-1)_+,\qquad\mathrm{Light}(a)=|\{\{a;b,b';c\}\in X(2):b,b'\in\mathrm{Ch}(a),c\in L\}|,$$
--
--   with $\|\mathrm{Same}_i\|=\sum_{a\in H_i}\|a\|\mathrm{Same}(a)$ and $\|\mathrm{Light}_i\|$ alike. These quantities organize the local-to-global argument of Section 4.
--
--   **Formalization Note.** $H_I$ is defined by recursion on $r-|I|$. $H_r(t)=H_r\cap H(t)$ and $\|\mathrm{Same}_i\|$, $\|\mathrm{Light}_i\|$ are not defined in print; their use on pp.29–32 and p.39 fixes these readings. $\mathrm{Ter}(v)$ is defined by recursion with the level of $v$ as fuel. $E$ is real-valued. A square is a set of four vertices, so each is counted once, and $\mathrm{Light}$ vanishes on $H_0,H_1$ automatically.
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), §4.1, pp.28–29, eqs. (4.1)–(4.6); §4.3, p.31, eqs. (4.10), (4.11); p.32

import Mathlib
import Definitions.Def_LosslessQLTC_normC

namespace LosslessQLTC

variable {k : ℕ}

/-- The support of a cochain, as a vertex set: `H_r = supp f`, the initial heavy set (p.28 of
arXiv:2610.00525, held version, sha256 d61f0ed9…). -/
def supportSet (X : SquareComplex k) {r : ℕ} (f : Level X r → ZMod 2) : Finset X.Vtx :=
  (Finset.univ.filter fun v : Level X r => f v ≠ 0).map ⟨Subtype.val, Subtype.val_injective⟩

/-- `u_j(x) = d_j(x) / D_j` of (4.1), p.28, where `d_j(x)` counts the parents `y` of `x` in
direction `j` that lie in `A`. -/
noncomputable def heavyU (X : SquareComplex k) (A : Finset X.Vtx) (x : X.Vtx) (j : Fin k) : ℝ :=
  ((A.filter fun y => X.up x y ∧ X.type y = insert j (X.type x)).card : ℝ) / (X.D j : ℝ)

/-- The heavy set at level `r − n`, `n ≤ r`: `H_r = supp f` at `n = 0`, and (4.2), p.28, below it:
`x` of level `i = r − n` is heavy if `Σ_{j ∉ type x} u_j(x) ≥ γ_i`.

**Formalization Note.** A recursion on the distance `n` from level `r`. The guard `n + 1 ≤ r`
makes the set empty below level `0`, so that the subtraction `r − (n + 1)` is the true level. -/
noncomputable def heavyBelow (X : SquareComplex k) {r : ℕ} (f : Level X r → ZMod 2)
    (γ : ℕ → ℝ) : ℕ → Finset X.Vtx
  | 0 => supportSet X f
  | n + 1 => Finset.univ.filter fun x =>
      n + 1 ≤ r ∧ (X.type x).card = r - (n + 1) ∧
        γ (r - (n + 1)) ≤ ∑ j ∈ Finset.univ \ X.type x, heavyU X (heavyBelow X f γ n) x j

/-- The heavy set `H_i` at level `i`, for `0 ≤ i ≤ r + 1`: (4.2) for `i < r`; `H_r = supp f`;
and (4.3) for `i = r + 1`: `H_{r+1} = {v ∈ V_{r+1} : a ⋖ v for some a ∈ H_r}` (p.28). -/
noncomputable def heavyLevel (X : SquareComplex k) {r : ℕ} (f : Level X r → ZMod 2)
    (γ : ℕ → ℝ) (i : ℕ) : Finset X.Vtx :=
  if i = r + 1 then Finset.univ.filter fun v => ∃ a ∈ supportSet X f, X.up a v
  else if i ≤ r then heavyBelow X f γ (r - i) else ∅

/-- `H = ⋃_{i=0}^{r+1} H_i` (p.28). The light set is its complement, `L = X(0) ∖ H`. -/
noncomputable def heavy (X : SquareComplex k) {r : ℕ} (f : Level X r → ZMod 2) (γ : ℕ → ℝ) :
    Finset X.Vtx :=
  (Finset.range (r + 2)).biUnion (heavyLevel X f γ)

/-- The heavy children `Ch(v) = {u ∈ H_{i−1} : u ⋖ v}` of `v ∈ H_i` (p.28). Since `u ⋖ v` forces
`u` to have level `i − 1`, this is empty for `i = 0`, as the source sets. -/
noncomputable def Ch (X : SquareComplex k) {r : ℕ} (f : Level X r → ZMod 2) (γ : ℕ → ℝ)
    (v : X.Vtx) : Finset X.Vtx :=
  (heavy X f γ).filter fun u => X.up u v

/-- `Ter = {v ∈ H : Ch(v) = ∅}` (Definition 4.1, p.28). -/
noncomputable def terminals (X : SquareComplex k) {r : ℕ} (f : Level X r → ZMod 2) (γ : ℕ → ℝ) :
    Finset X.Vtx :=
  (heavy X f γ).filter fun v => Ch X f γ v = ∅

/-- The recursion (4.4) with a fuel argument: `{v}` if `v` is terminal, and the union of the values
at its heavy children otherwise. -/
noncomputable def terAux (X : SquareComplex k) {r : ℕ} (f : Level X r → ZMod 2) (γ : ℕ → ℝ) :
    ℕ → X.Vtx → Finset X.Vtx
  | 0, v => if v ∈ terminals X f γ then {v} else ∅
  | n + 1, v => if v ∈ terminals X f γ then {v}
      else (Ch X f γ v).biUnion (terAux X f γ n)

/-- `Ter(v)`, eq. (4.4), p.29. The fuel is the level of `v`, which bounds the length of a downward
path, since a child's level is one less. -/
noncomputable def terOf (X : SquareComplex k) {r : ℕ} (f : Level X r → ZMod 2) (γ : ℕ → ℝ)
    (v : X.Vtx) : Finset X.Vtx :=
  terAux X f γ (X.type v).card v

/-- The terminal cluster `H(t) = {a ∈ H : t ∈ Ter(a)}`, eq. (4.5), p.29. -/
noncomputable def cluster (X : SquareComplex k) {r : ℕ} (f : Level X r → ZMod 2) (γ : ℕ → ℝ)
    (t : X.Vtx) : Finset X.Vtx :=
  (heavy X f γ).filter fun a => t ∈ terOf X f γ a

/-- The cochain `H_r(t) = H_r ∩ H(t)`.

**Formalization Note.** The source never defines `H_r(t)` in print; its use on pp.29–30 and p.39
fixes this reading. -/
noncomputable def clusterCochain (X : SquareComplex k) {r : ℕ} (f : Level X r → ZMod 2)
    (γ : ℕ → ℝ) (t : X.Vtx) : Level X r → ZMod 2 :=
  fun v => if v.1 ∈ supportSet X f ∧ v.1 ∈ cluster X f γ t then 1 else 0

/-- The excess `E(a) = |Ter(a)| − 1`, eq. (4.6), p.29, as a real number. -/
noncomputable def excess (X : SquareComplex k) {r : ℕ} (f : Level X r → ZMod 2) (γ : ℕ → ℝ)
    (a : X.Vtx) : ℝ :=
  ((terOf X f γ a).card : ℝ) - 1

/-- `∥E_i∥ = Σ_{a ∈ H_i} E(a) ∥a∥` (p.29). -/
noncomputable def excessNorm (X : SquareComplex k) {r : ℕ} (f : Level X r → ZMod 2) (γ : ℕ → ℝ)
    (i : ℕ) : ℝ :=
  ∑ a ∈ heavyLevel X f γ i, excess X f γ a * weight X a

/-- The same-type excess (4.10), p.31: `Same(a) = Σ_{|J| = i−1} (|Ch(a) ∩ H_J| − 1)_+` for
`a ∈ H_i`, `i ≥ 1`, and `Same(a) = 0` for `a ∈ H_0`. -/
noncomputable def same (X : SquareComplex k) {r : ℕ} (f : Level X r → ZMod 2) (γ : ℕ → ℝ)
    (a : X.Vtx) : ℝ :=
  if (X.type a).card = 0 then 0
  else ∑ J ∈ Finset.powersetCard ((X.type a).card - 1) Finset.univ,
    max ((((Ch X f γ a).filter fun u => X.type u = J).card : ℝ) - 1) 0

open scoped Classical in
/-- The light squares (4.11), p.31: `Light(a) = |{{a; b, b′; c} ∈ X(2) | b, b′ ∈ Ch(a), c ∈ L}|`.
A square is a set of four vertices (Definition 2.3), so each is counted once. A declared square
with top `a` needs `a` at level at least `2`, so `Light(a) = 0` on `H_0` and `H_1`, as the source
sets. -/
noncomputable def light (X : SquareComplex k) {r : ℕ} (f : Level X r → ZMod 2) (γ : ℕ → ℝ)
    (a : X.Vtx) : ℝ :=
  (((Finset.univ : Finset (Finset X.Vtx)).filter fun Q =>
    ∃ b b' c, Q = {a, b, b', c} ∧ X.Square a b b' c ∧ b ∈ Ch X f γ a ∧ b' ∈ Ch X f γ a ∧
      c ∉ heavy X f γ).card : ℝ)

/-- `∥Same_i∥ = Σ_{a ∈ H_i} ∥a∥ Same(a)` (Theorem 4.4's proof, p.32). -/
noncomputable def sameNorm (X : SquareComplex k) {r : ℕ} (f : Level X r → ZMod 2) (γ : ℕ → ℝ)
    (i : ℕ) : ℝ :=
  ∑ a ∈ heavyLevel X f γ i, weight X a * same X f γ a

/-- `∥Light_i∥ = Σ_{a ∈ H_i} ∥a∥ Light(a)` (Theorem 4.4's proof, p.32). -/
noncomputable def lightNorm (X : SquareComplex k) {r : ℕ} (f : Level X r → ZMod 2) (γ : ℕ → ℝ)
    (i : ℕ) : ℝ :=
  ∑ a ∈ heavyLevel X f γ i, weight X a * light X f γ a

/-- The thresholds of p.28: `0 < γ_i < k − i` for `0 ≤ i < r`. -/
def IsThresholds (k r : ℕ) (γ : ℕ → ℝ) : Prop :=
  ∀ i, i < r → 0 < γ i ∧ γ i < (k : ℝ) - i

end LosslessQLTC


