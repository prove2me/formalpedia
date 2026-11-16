-- Prove2me | Definitions.Def_WICanon_Supplement_OracleMachine
-- name    : WICanon_Supplement_OracleMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:52:58.081098+00:00
-- url     : https://prove2.me/theorems/8ee8f204-ed90-4962-9e4c-f8b58f74f8c5
-- title:
--   No-input randomized oracles and PPT machines with oracle access
-- statement:
--   A **no-input randomized oracle** $\mathcal O$ (Definition A.4) is a family of distributions $D=\{D_m\}_{m\in\mathbb N}$: on input $1^m$ it returns a fresh, independent sample $y\leftarrow D_m$.
--
--   A **non-uniform PPT machine with oracle access to $\mathcal O$** consists of a polynomial-time map, an advice string $a_n$ of length at most a polynomial in $n$, a polynomial number of coins and a polynomial bound $T$ on its number of queries. On security parameter $n$ and input $x$, with $N=n+|x|$, it reads $\mathrm{coins}(N)$ uniform coins and the answers to up to $T(N)$ queries $1^m$ of each length $m\le T(N)$, every answer an independent sample of $D_m$, and outputs the map applied to $(a_n,1^n,x,\text{coins},\text{answers})$. A **uniform** machine has empty advice.
--
--   The output law of $\mathcal M^{\mathcal O}$ is taken over its coins and its oracle answers, and $\Pr[\mathcal M^{\mathcal O}(x)=1]$ is the probability that it outputs the bit $1$.
--
--   These machines are the distinguishers of Definition A.2 and the algorithms $\mathsf{Enc}$, $\mathsf{Dec}$ and the adversaries of Definition A.3.
--
--   **Formalization Note** Oracle access is modelled by handing the machine a table of $T(T+1)$ independent answers, the $j$-th query $1^m$ reading entry $(j,m)$; this is the same as asking the queries one at a time. The machine's running time is polynomial in its whole input, the answers included. For the hard oracles of this mission an answer to $1^m$ has length linear in $m$, so the time is polynomial in $N$. A machine never sees more than polynomially many samples.
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Definition A.4, p.38; Definitions A.2–A.3, p.38; §2, p.11

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_RegevRecon_Law
import Definitions.Def_WICanon_Law

set_option autoImplicit false

namespace WICanon.Supplement

open QAlgorithms.Complexity QAdvFew.PoQOracle QiOPoQ

/-- **A no-input randomized oracle** (Arnon, Mazor, Pass, Silbak, *Does Witness Indistinguishability
Require Cryptography?*, STOC 2027 submission manuscript, sha256 3f78ec3d…, Definition A.4, p.38: "there
exists a family of distribution D = {D_n}_{n∈N} such that on input 1^n, O outputs an independent sample
of y ← D_n"). `O m` is the law `D_m` of the answer to the query `1^m`. -/
abbrev NoInputOracle := ℕ → Law

/-- The answers to the queries of a machine that may ask each of `1^0, …, 1^T` up to `T` times: a
table of `T·(T+1)` independent samples, the entry `j·(T+1) + m` (`j < T`, `m ≤ T`) drawn from `O m` and
answering the `j`-th query `1^m`. The table is handed over as one string, `tup` of its entries. -/
noncomputable def oracleTape (O : NoInputOracle) (T : ℕ) : Law :=
  RegevRecon.Law.map (fun t : Fin (T * (T + 1)) → Str => tup (List.ofFn t))
    (RegevRecon.Law.indep (T * (T + 1)) fun k => O (k.val % (T + 1)))

/-- **A non-uniform PPT machine with oracle access to a no-input oracle** (§2, p.11; Definitions A.2,
A.3, p.38). It has a polynomial-time map `run`, an advice string `advice n` of length at most
`adviceLen(n)` for each parameter `n`, a polynomial number of coins and a polynomial query bound. On
parameter `n` and input `x`, with `N = n + |x|`, it reads `coins(N)` uniform coins `r` and the answers
`t` of `queries(N)` queries of each length `m ≤ queries(N)` (`oracleTape`), and outputs
`run (pair (advice n) (pair 1^n (pair x (pair r t))))`.

**Formalization Note.** Oracle access is modelled by handing the machine fresh independent answers to
every query it could make: a machine running in time `T` asks at most `T` queries, each of length at
most `T`, and each query returns a new sample (Definition A.4). Reading answers from the table is the
same as asking the queries. The number of samples is polynomial and `run` is polynomial-time in its
whole input, the samples included; for the hard oracles of this mission every sample `(x, w)` to a
query `1^m` has length linear in `m`, so the running time is polynomial in `N`. -/
structure OracleMachine where
  run : Str → Str
  run_poly : PolyTimeComputable run
  advice : ℕ → Str
  adviceLen : Polynomial ℕ
  advice_le : ∀ n, (advice n).length ≤ adviceLen.eval n
  coins : Polynomial ℕ
  queries : Polynomial ℕ

namespace OracleMachine

/-- A uniform machine: it gets no advice. -/
def IsUniform (M : OracleMachine) : Prop := ∀ n, M.advice n = []

/-- The law of the output of `M^O` on parameter `n` and input `x`, over its coins and its oracle
answers. -/
noncomputable def outLaw (O : NoInputOracle) (M : OracleMachine) (n : ℕ) (x : Str) : Law :=
  bindLaw (oracleTape O (M.queries.eval (n + x.length))) fun t =>
    coinLaw (M.coins.eval (n + x.length)) fun r =>
      M.run (pair (M.advice n) (pair (unary n) (pair x (pair r t))))

/-- `Pr[M^O(x) = 1]` on parameter `n`. -/
noncomputable def accProb (O : NoInputOracle) (M : OracleMachine) (n : ℕ) (x : Str) : ℝ :=
  expect (M.outLaw O n x) fun o => if o = bitStr true then 1 else 0

end OracleMachine

end WICanon.Supplement


