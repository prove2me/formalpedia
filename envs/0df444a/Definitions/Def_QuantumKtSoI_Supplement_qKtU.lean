-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_qKtU
-- name    : QuantumKtSoI_Supplement_qKtU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:31:34.684846+00:00
-- url     : https://prove2.me/theorems/a09a3523-731f-4bc4-adf6-eee6da07a3cd
-- title:
--   The program measure $\mathrm{qKt}_U$; polynomially universal and quasi-linear universal machines; the properties of Theorem D.30, Equation (36) and Lemma F.7
-- statement:
--   For a machine $U$ of Definition 3.1 the measure defined by its programs is
--   $$\mathrm{qKt}_U(y|x)=\min_{p,t}\{|p|+\lceil\log t\rceil : p\in\{0,1\}^*,\ t\ge1,\ P_U(\langle p,x\rangle;t,y)\ge 2/3\},$$
--   with the minimum of the empty set equal to $+\infty$ and $\mathrm{qKt}_U(y)=\mathrm{qKt}_U(y|\epsilon)$.
--
--   1. $U$ is **polynomially universal** (Equation (23)) with positive integers $k_U,C_U,d_U$ if every description $e$ has a program $p_e$ with $|p_e|\le|e|+k_U$ and $P_U(\langle p_e,x\rangle;C_U(t+|e|+|x|+1)^{d_U},y)\ge P_e(x;t,y)$ for all $x,y$ and $t\ge1$.
--   2. $U$ is **quasi-linear universal** (Definition 9.1, condition (U-a)) if there are constants $c_a,c'_a\ge1$ such that for every machine $M$, all strings $w,x,y$ and every $t\ge1$,
--   $$P_U\big(\langle\overline{\ulcorner M\urcorner}\,w,x\rangle;c_M(t+|x|+|w|+1)\lceil\log(t+2)\rceil,y\big)\ge P_M(\langle w,x\rangle;t,y),\qquad c_M=c_a(|\ulcorner M\urcorner|+2)^{c'_a}.$$
--   3. A machine $I$ and a polynomial $p_I$ with nonnegative coefficients have the **Theorem D.30 property** if $P_I(\langle e,x\rangle;p_I(|e|+\log(t+|x|+2))(t+|x|+|e|+1),y)\ge P_e(x;t,y)$ for every description $e$, all $x,y$ and $t\ge1$.
--   4. **Equation (36)** for $I$ and $U$: there are $\gamma_U\ge1$, $\ell_U,\delta_U\ge0$ with $P_U(\langle\overline{\ulcorner I\urcorner}\,w,x\rangle;\gamma_U(|x|+|w|+2)^{\delta_U}(t+|x|+|w|+1)\lceil\log(t+2)\rceil^{\ell_U},y)\ge P_I(\langle w,x\rangle;t,y)$.
--   5. The **Lemma F.7 properties** of $U$ with integers $k\ge2$, $c_U\ge1$: (i) $P_U(\langle p,y\rangle;t,w)=0$ for $t\ge1$ if $p$ is not a description; (ii) $P_U(\langle p,y\rangle;c_U(|p|+|y|+s+2)^k,w)\ge P_p(y;s,w)$ for $s\ge0$ if $p$ is a description; (iii) $P_U(\langle p,y\rangle;t,w)\le P_p(y;\lfloor(kt)^{1/k}\rfloor,w)$ for $t\ge1$ if $p$ is a description.
--
--   These are the objects of the model-dependence results of §9 and Appendices D and F.
--
--   **Formalization Note** $\mathrm{qKt}_U$ takes values in $\mathbb N\cup\{\infty\}$ (`ℕ∞`), whose infimum of the empty set is $\infty$. Machines are valid coded machines, $\ulcorner M\urcorner$ is the published encoding and $\overline{\ulcorner M\urcorner}$ its self-delimiting code (§2.1, the published `sd`), so the program $\overline{\ulcorner M\urcorner}\,w$ is `sd M.encode ++ w`; real deadlines are floors, and descriptions and $P_e$ are those of a glue routine set $G$.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), §9, pp.117–118 (qKt_U, Equation (23), Definition 9.1); Theorem D.30, p.181; Equation (36), p.186; Lemma F.7, p.242

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_Desc

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-- The **program measure** of a machine `U` of Definition 3.1 (§9, p.117 of Myrisiotis, STOC 2027
submission, held version sha256 6616571c…):
`qKt_U(y | x) = min_{p,t} { |p| + ⌈log t⌉ : p ∈ {0,1}*, t ≥ 1, P_U(⟨p, x⟩; t, y) ≥ 2/3 }`,
with the minimum of the empty set taken to be `+∞`; `qKt_U(y) = qKt_U(y | ε)` is `qKtU U y []`.

**Formalization Note** The value lies in `ℕ∞`, whose `sInf ∅` is `⊤ = +∞`, exactly as the paper
specifies; `⌈log t⌉` is `Nat.clog 2 t`. -/
def qKtU (U : CodedMachine) (y x : List Bool) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ p : List Bool, ∃ t : ℕ, 1 ≤ t ∧
    (2 / 3 : ℝ) ≤ U.toMachine.outputProb (pair p x) t y ∧ n = ((p.length + Nat.clog 2 t : ℕ) : ℕ∞)}

/-- `U` is **polynomially universal** with constants `k_U, C_U, d_U` (Equation (23), pp.117–118):
for every description `e` there is a program `p_e` with `|p_e| ≤ |e| + k_U` and
`P_U(⟨p_e, x⟩; C_U(t + |e| + |x| + 1)^{d_U}, y) ≥ P_e(x; t, y)` for all strings `x, y` and integers
`t ≥ 1`. `U` is a machine of Definition 3.1 (a valid coded machine). -/
def PolyUniversal (G : GlueRoutines) (U : CodedMachine) (kU CU dU : ℕ) : Prop :=
  U.Valid ∧ ∀ e : Desc, ∃ pe : List Bool, pe.length ≤ e.bits.length + kU ∧
    ∀ x y : List Bool, ∀ t : ℕ, 1 ≤ t →
      e.prob G x t y ≤
        U.toMachine.outputProb (pair pe x) (CU * (t + e.bits.length + x.length + 1) ^ dU) y

/-- **Definition 9.1** (Quasi-linear universal machine, p.117): `U` satisfies condition (U-a) if
there are constants `c_a, c′_a ≥ 1` such that, for every machine `M` of Definition 3.1 (a valid
coded machine), all strings `w, x, y` and every integer `t ≥ 1`,
`P_U(⟨⌜M⌝‾w, x⟩; c_M(t + |x| + |w| + 1)⌈log(t + 2)⌉, y) ≥ P_M(⟨w, x⟩; t, y)` with
`c_M = c_a(|⌜M⌝| + 2)^{c′_a}`, where the program `⌜M⌝‾w` is the self-delimiting code (§2.1, p.14) of
the encoding of `M`, followed by `w`.

**Formalization Note** `⌜M⌝` is the published encoding `CodedMachine.encode` and `⌜M⌝‾` is its
published self-delimiting code `sd`; the real deadline is
read as `⌊·⌋` (p.22). The constants are taken real. -/
def QuasiLinUniversal (U : CodedMachine) : Prop :=
  U.Valid ∧ ∃ ca ca' : ℝ, 1 ≤ ca ∧ 1 ≤ ca' ∧ ∀ M : CodedMachine, M.Valid → ∀ w x y : List Bool, ∀ t : ℕ,
    1 ≤ t →
      M.toMachine.outputProb (pair w x) t y ≤
        U.toMachine.outputProbR (pair (sd M.encode ++ w) x)
          (ca * ((M.encode.length : ℝ) + 2) ^ ca' * ((t : ℝ) + x.length + w.length + 1) *
            (Nat.clog 2 (t + 2) : ℝ)) y

/-- The property of the machine `I` and the polynomial `p_I` in **Theorem D.30** (p.181): `p_I` has
nonnegative coefficients and, for every description `e`, all strings `x, y` and every integer
`t ≥ 1`, `P_I(⟨e, x⟩; p_I(|e| + log(t + |x| + 2))(t + |x| + |e| + 1), y) ≥ P_e(x; t, y)`.

**Formalization Note** The input `⟨e, x⟩` pairs the bit string of `e`; the real deadline is read
as `⌊·⌋` (p.22); `p_I` is a real polynomial evaluated at a real argument. -/
def InterpreterProp (G : GlueRoutines) (I : CodedMachine) (pI : Polynomial ℝ) : Prop :=
  I.Valid ∧ (∀ n, 0 ≤ pI.coeff n) ∧ ∀ e : Desc, ∀ x y : List Bool, ∀ t : ℕ, 1 ≤ t →
    e.prob G x t y ≤
      I.toMachine.outputProbR (pair e.bits x)
        (pI.eval ((e.bits.length : ℝ) + Real.logb 2 ((t : ℝ) + x.length + 2)) *
          ((t : ℝ) + x.length + e.bits.length + 1)) y

/-- **Equation (36)** (Corollary D.39, p.186) for machines `I` and `U`: there are constants
`γ_U ≥ 1` and `ℓ_U, δ_U ≥ 0` such that, for all strings `w, x, y` and every integer `t ≥ 1`,
`P_U(⟨⌜I⌝‾w, x⟩; γ_U(|x| + |w| + 2)^{δ_U}(t + |x| + |w| + 1)⌈log(t + 2)⌉^{ℓ_U}, y) ≥ P_I(⟨w, x⟩; t, y)`,
where `⌜I⌝‾` is the self-delimiting code `sd` of the published encoding of `I`.
The real deadline is read as `⌊·⌋` (p.22). -/
def Eq36 (I U : CodedMachine) : Prop :=
  U.Valid ∧ ∃ γU lU δU : ℝ, 1 ≤ γU ∧ 0 ≤ lU ∧ 0 ≤ δU ∧ ∀ w x y : List Bool, ∀ t : ℕ, 1 ≤ t →
    I.toMachine.outputProb (pair w x) t y ≤
      U.toMachine.outputProbR (pair (sd I.encode ++ w) x)
        (γU * ((x.length : ℝ) + w.length + 2) ^ δU * ((t : ℝ) + x.length + w.length + 1) *
          (Nat.clog 2 (t + 2) : ℝ) ^ lU) y

/-- Properties (i)–(iii) of the padded universal machine of **Lemma F.7** (p.242), for a machine
`U` and integers `k ≥ 2`, `c_U ≥ 1`, for all strings `p, y, w`:
(i) if `p` is not a description string, `P_U(⟨p, y⟩; t, w) = 0` for every `t ≥ 1`;
(ii) if `p = bits e`, then `P_U(⟨p, y⟩; c_U(|p| + |y| + s + 2)^k, w) ≥ P_e(y; s, w)` for every `s ≥ 0`;
(iii) if `p = bits e`, then `P_U(⟨p, y⟩; t, w) ≤ P_e(y; ⌊(kt)^{1/k}⌋, w)` for every `t ≥ 1`. -/
def PaddedUniversal (G : GlueRoutines) (U : CodedMachine) (k cU : ℕ) : Prop :=
  U.Valid ∧ 2 ≤ k ∧ 1 ≤ cU ∧
    (∀ p y w : List Bool, (∀ e : Desc, p ≠ e.bits) → ∀ t : ℕ, 1 ≤ t →
      U.toMachine.outputProb (pair p y) t w = 0) ∧
    (∀ e : Desc, ∀ y w : List Bool, ∀ s : ℕ,
      e.prob G y s w ≤ U.toMachine.outputProb (pair e.bits y) (cU * (e.bits.length + y.length + s + 2) ^ k) w) ∧
    (∀ e : Desc, ∀ y w : List Bool, ∀ t : ℕ, 1 ≤ t →
      U.toMachine.outputProb (pair e.bits y) t w ≤
        e.prob G y ⌊((k : ℝ) * t) ^ (1 / (k : ℝ))⌋₊ w)

end QuantumKtSoI.Supplement


