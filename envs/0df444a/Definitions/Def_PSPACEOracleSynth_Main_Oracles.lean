-- Prove2me | Definitions.Def_PSPACEOracleSynth_Main_Oracles
-- name    : PSPACEOracleSynth_Main_Oracles
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:01.103539+00:00
-- url     : https://prove2.me/theorems/f3c51f04-ed4c-4c9c-ad09-de8a4f1a3632
-- title:
--   Languages as oracles, $\mathsf{PSPACE}^A$-completeness, and entries computable in polynomial space (Definition 2.4)
-- statement:
--   Throughout, a **classical oracle** is a language $A\subseteq\{0,1\}^*$, identified with its characteristic function, and $\mathsf{PSPACE}^A$ is the class of languages decided by deterministic oracle machines that use polynomial space *including their query tape*.
--
--   1. For a language $L$, the oracle $\mathrm{langOracle}(L)$ answers a query $x$ with $[x\in L]$.
--   2. A language $K$ is **$\mathsf{PSPACE}^A$-complete** if $K\in\mathsf{PSPACE}^A$ and every $L\in\mathsf{PSPACE}^A$ reduces to $K$ by a polynomial-time many-one reduction computed *without access to $A$*: there is a polynomial-time computable $f:\{0,1\}^*\to\{0,1\}^*$ with
--   $$x\in L\iff f(x)\in K\qquad\text{for all }x.$$
--   3. (**Definition 2.4**) A unitary language $\mathcal U=(U_n)$ has **entries computable in polynomial space relative to $A$** if a deterministic polynomial-space algorithm with oracle $A$ (its *entry algorithm*) computes $\langle u|U_n|v\rangle$ to precision $t$ on input $(1^n,u,v,1^t)$, for $n\ge1$ and $u,v\in\{0,1\}^n$, with $O(t+1)$ bits per component: its output is a complex dyadic number $a+bi$ with
--   $$\bigl|a+bi-\langle u|U_n|v\rangle\bigr|\le 2^{-t},$$
--   and the binary codes of $a$ and $b$ have length at most $c(t+1)$ for a constant $c$ fixed with the algorithm.
--
--   These notions enter the main theorem (complete oracles) and Theorem 3.1 (its hypothesis).
--
--   **Formalization Note.** Oracles are `QAdvFew.PoQOracle.Oracle = Str → Bool`; $\mathsf{PSPACE}^A$ is the published `QAdvFew.PoQOracle.PSPACE A`, whose space count includes the query tape. The reduction is the oracle-free `PolyTimeComputable`. In Definition 2.4 the input $(1^n,u,v,1^t)$ is the `tup` encoding of the four strings ($u$ written $u_0u_1\cdots u_{n-1}$), the output is `tup [re, im]` with `re`, `im` fixed-point codes (published `fixedPoint`), and the machine, its polynomial space bound (in the input length) and the constant $c$ are chosen before $n,u,v,t$.
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), §2.1, p. 9 (classical oracles); §2.2, p. 11 (PSPACE^A, completeness); Definition 2.4, p. 11

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_Oracle
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_PSPACE
import Definitions.Def_KTUnitary_Synth_ULang
import Definitions.Def_KTUnitary_Synth_fixedPoint

open QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth

namespace PSPACEOracleSynth.Main

/-!
# Languages as oracles, PSPACE^A-completeness, entries computable in polynomial space

Sichen Wang, *Unitary Synthesis with a PSPACE Oracle*, STOC 2027 submission #1740 (October 2026),
§2.1–§2.3, pp. 9–11.

* `langOracle L` is the classical oracle (characteristic function) of a language `L ⊆ {0,1}*`
  (p. 9: "A classical oracle is a language `A ⊆ {0,1}*`").
* `IsPSPACECompleteRel A K`: `K ∈ PSPACE^A` and every `L ∈ PSPACE^A` reduces to `K` by a
  polynomial-time many-one reduction computed without access to `A` (p. 11).
* `HasPSpaceEntries A U`: Definition 2.4 (p. 11).
-/

open Classical in
/-- The classical oracle of a language `L`: `x ↦ [x ∈ L]`. -/
noncomputable def langOracle (L : Set Str) : Oracle := fun x => decide (x ∈ L)

/-- **PSPACE^A-completeness** (p. 11): "A language `K` is `PSPACE^A`-complete if it lies in
`PSPACE^A` and every language in `PSPACE^A` reduces to it by a polynomial-time many-one reduction
computed without access to `A`." The reduction `f` is polynomial-time computable by a machine with
no oracle. -/
def IsPSPACECompleteRel (A : Oracle) (K : Set Str) : Prop :=
  K ∈ PSPACE A ∧
    ∀ L ∈ PSPACE A, ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ x : Str, x ∈ L ↔ f x ∈ K

/-- The input `(1^n, u, v, 1^t)` of an entry algorithm, as one bit string: the `tup` encoding of
the four components, with `u, v ∈ {0,1}^n` written as their bit strings `u₀u₁⋯u_{n−1}`. -/
def entryInput {n : ℕ} (u v : Bits n) (t : ℕ) : Str :=
  tup [unary n, List.ofFn u, List.ofFn v, unary t]

/-- **Entries computable in polynomial space relative to `A`** (Definition 2.4, p. 11): "A unitary
language `U` has entries computable in polynomial space relative to `A` if a deterministic
polynomial-space algorithm with oracle `A`, its entry algorithm, computes `⟨u|U_n|v⟩` to precision
`t` on input `(1^n, u, v, 1^t)`, for `u, v ∈ {0,1}^n`, with `O(t + 1)` bits per component."

Here: one oracle machine `M`, one polynomial `p` and one constant `c` such that for every `n ≥ 1`,
all `u, v ∈ {0,1}^n` and every `t`, the run of `M^A` on `(1^n, u, v, 1^t)` halts at some step `T`
having used at most `p(input length)` cells (query tape included), and its output is the pair
`tup [re, im]` of fixed-point codes of a complex dyadic number within `2^{−t}` of the entry
`⟨u|U_n|v⟩` (row `u`, column `v`), each code of length at most `c (t + 1)`. -/
def HasPSpaceEntries (A : Oracle) (U : ULang) : Prop :=
  ∃ (M : OTM) (p : Polynomial ℕ) (c : ℕ), ∀ (n : ℕ), 1 ≤ n → ∀ (u v : Bits n) (t : ℕ),
    ∃ T : ℕ, M.result A (entryInput u v t) T ≠ none ∧
      M.space A (entryInput u v t) T ≤ p.eval (entryInput u v t).length ∧
      ∃ re im : Str, M.output A (entryInput u v t) T = tup [re, im] ∧
        re.length ≤ c * (t + 1) ∧ im.length ≤ c * (t + 1) ∧
        ‖((fixedPoint re : ℝ) : ℂ) + ((fixedPoint im : ℝ) : ℂ) * Complex.I
            - (U n : Matrix (Bits n) (Bits n) ℂ) u v‖ ≤ (2 : ℝ)⁻¹ ^ t

end PSPACEOracleSynth.Main


