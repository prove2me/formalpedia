-- Prove2me | Definitions.Def_AvgWorstGap_Program
-- name    : AvgWorstGap_Program
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:46:49.694411+00:00
-- url     : https://prove2.me/theorems/92744e4a-daa6-4463-9866-3faf5ec3cb15
-- title:
--   Programs in the composition model and their outputs
-- statement:
--   A **program** is a nonempty sequence of machine-advice pairs $\Pi=((M_1,\alpha_1),\dots,(M_\ell,\alpha_\ell))$. A pair $(M,\alpha)$ is encoded as
--   $$s_1\,01\,\langle M\rangle\,s_2\,01\,\alpha,$$
--   where $s_1$ (resp. $s_2$) is the binary representation of $|\langle M\rangle|$ (resp. $|\alpha|$) with each bit duplicated. The description of $\Pi$ is the concatenation of the encodings of its pairs, and $|\Pi|$ is its length.
--
--   The output of $\Pi$ on $(x;r)$ with oracle $O$ is computed in stages. $y_1$ is the output of $M_1(\alpha_1;x;r)$, and $t_1$ is the number of steps it takes. $y_2$ is the output of $M_2(\alpha_2;x\circ y_1;r[t_1+1:|r|])$, with running time $t_2$, and so on. Stage $i$ receives the auxiliary input $x\circ y_{i-1}$ and the randomness after the first $t_1+\cdots+t_{i-1}$ bits. The output is $y_\ell$ and the running time is $\sum_i t_i$. "$\Pi^O(y;\epsilon;r)$ outputs $z$ within $t$ steps" means that this staged run produces $z$ with total running time at most $t$.
--
--   **Formalization Note** Every stage runs with an empty guess tape. Each intermediate output must be a bit string. The empty program outputs nothing.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), §2.1, pp.12–13

import Mathlib
import Definitions.Def_NKtLB_Machine
import Definitions.Def_AvgWorstGap_pairStr
import Definitions.Def_AvgWorstGap_code

namespace AvgWorstGap

open NKtLB

/-- **Halting after exactly `t` steps with output `z`**: the machine `M` (the published
`NKtLB.Machine`) first reaches its halting state at step `t` (arXiv:2610.19162, version of
October 30, 2026, p.13: "the number of steps `M(α; x; r)` takes to produce `y`") and its output tape
then holds `z`. -/
def HaltsExactly (M : Machine) (O : Set (List Bool)) (inp : Inputs) (t : ℕ) (z : List Sym) :
    Prop :=
  (M.run O inp t).state = M.halt ∧ (∀ j < t, (M.run O inp j).state ≠ M.halt) ∧
    (M.run O inp t).output = z

/-- **Programs in the composition model** (arXiv:2610.19162, version of October 30, 2026, §2.1,
p.13): "a program `Π` is now defined as `Π := ((M1, α1), . . . , (Mℓ, αℓ))`, where each `Mi` is a
valid encoding of a machine and `αi ∈ {0, 1}∗`." -/
abbrev Program := List (Machine × List Bool)

/-- **The encoding of a machine-advice pair** (p.12): "`s1 01 ⟨M⟩ s2 01 α`, where `⟨M⟩` is an
encoding of the machine `M`, and `s1` (resp. `s2`) is the binary representation of the integer
specifying the length of `⟨M⟩` (resp. `α`), with each bit duplicated." Here `⟨M⟩ = code M`. -/
def pairEnc (p : Machine × List Bool) : List Bool :=
  dbl (bin (code p.1).length) ++ [false, true] ++ code p.1 ++ dbl (bin p.2.length) ++
    [false, true] ++ p.2

/-- **The description of a program** (p.13): "The full description of `Π` is obtained by
concatenating the encodings of all pairs `(Mi, αi)` for `i ∈ [ℓ]`. The size of `Π`, denoted
`|Π|`, is the total bit length of this description." -/
def progEnc (P : Program) : List Bool := P.flatMap pairEnc

/-- **The staged run of a program** (p.13): `RunsFrom O P base aux r T z` says that the stages
`P` run in turn with oracle `O`, the first one with auxiliary input `aux` and randomness `r`, and
produce the word `z` after `T` steps in total. "Let `y1` be the output of `M1(α1; x; r)`. Let `t1` be
the number of steps `M1(α1; x; r)` takes to produce `y1`. Let `y2` be the output of
`M2(α2; x ◦ y1; r[t1+1:|r|])`, … Output `yℓ`. The running time of the program `Π` on input `(x; r)`
is given by `Σ_{i=1}^ℓ ti`." Here `base` is `x`, and each later stage gets auxiliary input
`x ◦ y_{i−1}` and the randomness not yet skipped.

**Formalization Note.** Every stage runs with its advice on the input tape and an empty guess tape;
`ti` is the first step at which `Mi` halts; an intermediate output `yi` must be a bit string. The
empty program produces nothing. -/
def RunsFrom (O : Set (List Bool)) : Program → List Bool → List Bool → List Bool → ℕ →
    List Sym → Prop
  | [], _, _, _, _, _ => False
  | [p], _, aux, r, T, z => HaltsExactly p.1 O ⟨p.2, aux, [], r⟩ T z
  | p :: q :: rest, base, aux, r, T, z =>
      ∃ t : ℕ, ∃ y : List Bool, ∃ T' : ℕ,
        HaltsExactly p.1 O ⟨p.2, aux, [], r⟩ t (bitsSym y) ∧
        RunsFrom O (q :: rest) base (base ++ y) (r.drop t) T' z ∧ T = t + T'

/-- **`Π^O(y; ϵ; r)` outputs `z` within `t` steps** (Def. 2.1, p.13): the program `P` with oracle
`O`, auxiliary input `y` and randomness `r` produces `z` with total running time at most `t`. -/
def ProgOutputs (O : Set (List Bool)) (P : Program) (y r : List Bool) (t : ℕ) (z : List Sym) :
    Prop :=
  ∃ T ≤ t, RunsFrom O P y y r T z

end AvgWorstGap


