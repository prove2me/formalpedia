-- Prove2me | Definitions.Def_AvgWorstGap_InPSAMP
-- name    : AvgWorstGap_InPSAMP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:43.200625+00:00
-- url     : https://prove2.me/theorems/8436ce99-921d-401b-92fd-637dfe193496
-- title:
--   Polynomial-time samplable distribution families ($\mathsf{PSAMP}$) and the uniform family
-- statement:
--   A distribution family $D=\{D_n\}_{n\in\mathbb N}$ assigns to each $n$ a probability distribution on binary strings. $D$ is **polynomial-time samplable**, $D\in\mathsf{PSAMP}$, if there are a machine $M$ and a polynomial $p$ such that for every $n\in\mathbb N$ (including $n=0$, where $D_0$ is the output distribution of $M$ on the empty input $1^0$):
--
--   1. on input $1^n$ and every random string $r\in\{0,1\}^{p(n)}$, $M$ halts within $p(n)$ steps;
--   2. for every string $z$, $D_n(z)=\Pr_{r\sim\{0,1\}^{p(n)}}[M(1^n;r)\text{ outputs }z]$.
--
--   The **uniform family** $U$ has $U_n$ uniform on $\{0,1\}^n$.
--
--   **Formalization Note** Each $D_n$ is a probability mass function on `List Bool`. Sampling is exact. The paper writes "for every $n\ge1$"; the sampler is also required at $n=0$ because the heuristic schemes of $\mathsf{AvgBPP}$ quantify over every $n\in\mathbb N$, and an unconstrained $D_0$ of full support would put every $L$ with $(L,D)\in\mathsf{AvgBPP}$ into $\mathsf{BPP}$ (a reading, declared in every theorem that uses $\mathsf{PSAMP}$).
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), §2.5, p.17; Theorem 2.18, p.18

import Mathlib
import Definitions.Def_NKtLB_Machine
import Definitions.Def_NKtLB_tupleEnc
import Definitions.Def_AvgWorstGap_pairStr
import Definitions.Def_NKtLB_prob

namespace AvgWorstGap

open NKtLB

/-- **Polynomial-time samplable distribution families, `PSAMP`** (arXiv:2610.19162, version of
October 30, 2026, §2.5, p.17): "a distribution family `D = {Dn}n∈ℕ` is polynomial-time samplable if
there exists a randomized polynomial-time algorithm `A` such that for every `n ≥ 1`, the output of
`A(1^n)` is distributed according to `Dn`. We let PSAMP be the collection of distribution families
that can be sampled in polynomial time."

**Formalization Note.** `D n` is a probability mass function on binary strings. Samplability: a
machine `M` and a polynomial `p` such that for every `n ∈ ℕ`, on input `1^n` and every random string
`r ∈ {0,1}^{p(n)}`, `M` halts within `p(n)` steps, and `D_n(z)` equals the probability that the
output is `z`. Sampling is exact. The sampler is required for `n = 0` too (`D_0` is the output
distribution of `A(1^0) = A(ϵ)`), although the paper writes "for every `n ≥ 1`": the heuristic
schemes of `AvgBPP` (p.18) quantify over every `n ∈ ℕ`, and an unconstrained `D_0` of full support
would force every `(L, D) ∈ AvgBPP` to have `L ∈ BPP`, collapsing `DistPH ⊆ AvgBPP` to
`PH ⊆ BPP`. -/
def InPSAMP (D : ℕ → PMF (List Bool)) : Prop :=
  ∃ (M : Machine) (p : Polynomial ℕ), ∀ n : ℕ,
    (∀ r : List Bool, r.length = p.eval n →
      (M.run ∅ ⟨unary n, [], [], r⟩ (p.eval n)).state = M.halt) ∧
    ∀ z : List Bool, D n z =
      ENNReal.ofReal (prob (p.eval n) (fun r => M.HaltsWith ∅ ⟨unary n, [], [], r⟩ (p.eval n)
        (bitsSym z)))

/-- **The uniform family `U`** (p.18, Theorem 2.18; p.12: "`Uℓ` … the uniform distribution over
`{0, 1}^ℓ`"): `U_n` is uniform on the strings of length `n`. -/
noncomputable def uniformFamily (n : ℕ) : PMF (List Bool) :=
  (PMF.uniformOfFintype (Fin n → Bool)).map List.ofFn

end AvgWorstGap


