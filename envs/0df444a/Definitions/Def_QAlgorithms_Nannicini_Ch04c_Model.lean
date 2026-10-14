-- Prove2me | Definitions.Def_QAlgorithms_Nannicini_Ch04c_Model
-- name    : QAlgorithms_Nannicini_Ch04c_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:43:56.468001+00:00
-- url     : https://prove2.me/theorems/e90d61ec-0f58-4702-8d18-5a3a4215aaea
-- title:
--   Nannicini Ch04c: supporting definitions
-- statement:
--   Nannicini, Chapter 4 (part c): searching when the number of marked items is not known
--
--   ## QAlgorithms.Nannicini.mfStepGates
--
--   For arbitrary natural numbers $n,b$, this defines the natural number $3n+2b+1$, including $n=0$ and $b=0$; no bound or positivity assumption on either parameter is imposed.
--
--   ## QAlgorithms.Nannicini.mfRoundOverhead
--
--   For any natural number $m$, this defines $m+\lfloor m(m+1)/2\rfloor$ using natural-number division; because $m(m+1)$ is even, the second term is exactly $m(m+1)/2$. At $m=0$ the result is $0$.
--
--   ## QAlgorithms.Nannicini.alg1RoundList
--
--   For every natural number $n$, this is the list formed by taking $i=0,\ldots,n-2$ in increasing order and appending the two entries $i+1,i+1$ for each $i$, namely $[1,1,2,2,\ldots,n-1,n-1]$ when $n\geq2$. The subtraction $n-1$ is truncated natural-number subtraction, so the list is empty for both $n=0$ and $n=1$.
--
--   ## QAlgorithms.Nannicini.alg1Gates
--
--   For arbitrary natural numbers $n,b$, a list $L$ of natural numbers, and a natural number $c$, define $s=3n+2b+1$ and $h(m)=m+\lfloor m(m+1)/2\rfloor$. This recursive function is $0$ when $c=0$, regardless of $L$; for positive $c$ and an empty list it is $cs$; for positive $c$ and $L=m::L'$, it is $h(m)+cs$ if $c\leq2^m$, and otherwise $h(m)+2^ms+G(L',c-2^m)$, where $G$ denotes the same recursive function. The entire overhead of a head round is included even if $0<c<2^m$; at $c=2^m$ the tail is unused. Lists may be arbitrary, including entries $m=0$, and no positivity restriction is imposed on $n,b$.
--
--   ## QAlgorithms.Nannicini.minFindLoop
--
--   For any natural number $n$, any integer-valued function $f$ on $n$-bit strings, any natural parameters $b,T$, fuel $u$, incumbent $l$, counters $q,g\in\mathbb N$, and output $o=(l',q',g')$, this defines a weight in $[0,\infty]$ recursively. At $u=0$ it is $\mathbf1\{o=(l,q,g)\}$. At $u+1$, sum over all $\mathrm{oc}=(a,c)\in(\mathrm{Option}(\{0,1\}^n))\times\mathbb N$ the search weight for the Boolean predicate $F(j)=[f(j)<f(l)]$ times the following factor: if $q+c\leq T$, recur with fuel $u$, incumbent $k$ when $a=\mathrm{some}(k)$ and $f(k)<f(l)$ and incumbent $l$ otherwise, counters $q+c$ and $g+G(L_n,c)+s$; otherwise use $\mathbf1\{o=(l,T,g+G(L_n,T-q))\}$. Here $s=3n+2b+1$, $L_n=[1,1,\ldots,n-1,n-1]$ (empty for $n\leq1$), and $G(L,0)=0$, $G([],c)=cs$ for $c>0$, while $G(m::L,c)=h(m)+cs$ for $0<c\leq2^m$ and $h(m)+2^ms+G(L,c-2^m)$ otherwise, with $h(m)=m+\lfloor m(m+1)/2\rfloor$. The search weight starts at accumulated cost $0$ on $L_n$: at head $m$, draw $j$ with weight $w_m(j)=\sum_{a\in\{0,1\}^m}|\chi_m(a,j)|^2$, add $2^m$ to its cost, stop with $\mathrm{some}(j)$ if $F(j)$ is true, and otherwise continue to the tail; at the empty list, return the true $j$ of least binary integer value $B(j)=\sum_{i<n}[j_i]2^{n-1-i}$ at added cost $B(j)+1$, or return none at added cost $2^n$ if there is no true input. Explicitly $\chi_m=(Q_m^*\otimes I)D_m(A)(Q_m\otimes I)(|0^m\rangle\otimes H_n|0^n\rangle)$, where $Q_m(a,a')=2^{-m/2}e^{2\pi iB(a)B(a')/2^m}$, $D_m(A)$ keeps the first register fixed and applies $A^{B(a)}$ to the second, $A=H_nR_0H_n^*R_F$, $H_n(y,z)=2^{-n/2}(-1)^{\sum_i y_iz_i}$, $R_0$ has diagonal $+1$ at the all-false string and $-1$ elsewhere, and $R_F$ has diagonal $-1$ on true inputs and $+1$ otherwise. The infinite sum is in nonnegative extended reals. No initial bound $q\leq T$ is required, so $T-q$ is truncated to $0$ when $q>T$; the over-budget branch retains $l$, records exactly $T$, and does not add the extra $s$. All zero parameters and arbitrary output counters are included.
--
--   ## QAlgorithms.Nannicini.minFindWeight
--
--   For every natural number $n$, integer-valued function $f$ on $n$-bit strings, natural numbers $b,T$, and output triple $o$ of an $n$-bit string and two natural counters, this is the nonnegative extended-real sum $\sum_l2^{-n}K(T+1,l,0,0;o)$ over all $n$-bit incumbents $l$. The kernel $K(u,l,q,g;o)$ at zero fuel is the indicator of $o=(l,q,g)$; at positive fuel it sums over the search result $(a,c)$ for the predicate $F(j)=[f(j)<f(l)]$, multiplying its weight by $K(u-1,l_a,q+c,g+G(L_n,c)+s;o)$ when $q+c\leq T$, where $l_a=k$ if $a=\mathrm{some}(k)$ and $f(k)<f(l)$ and $l_a=l$ otherwise, and by the indicator of $o=(l,T,g+G(L_n,T-q))$ otherwise. Here $s=3n+2b+1$, $L_n$ lists each integer from $1$ to $n-1$ twice and is empty for $n\leq1$, $h(m)=m+\lfloor m(m+1)/2\rfloor$, and $G(L,0)=0$, $G([],c)=cs$ for $c>0$, $G(m::L,c)=h(m)+cs$ for $0<c\leq2^m$, or $h(m)+2^ms+G(L,c-2^m)$ when $c>2^m$. Search starts at cost $0$ and traverses $L_n$, at head $m$ sampling $j$ with weight $\sum_a|\chi_m(a,j)|^2$, adding $2^m$, terminating with that $j$ if $F(j)$ is true, and continuing otherwise; after all heads it deterministically returns the true input of least binary value $B(j)=\sum_{i<n}[j_i]2^{n-1-i}$ with additional cost $B(j)+1$, or none with additional cost $2^n$. Its state is $\chi_m=(Q_m^*\otimes I)D_m(H_nR_0H_n^*R_F)(Q_m\otimes I)(|0^m\rangle\otimes H_n|0^n\rangle)$, with $Q_m(a,a')=2^{-m/2}e^{2\pi iB(a)B(a')/2^m}$, $D_m(A)$ applying $A^{B(a)}$ conditioned on first register $a$, $H_n(y,z)=2^{-n/2}(-1)^{\sum_i y_iz_i}$, $R_0$ diagonal $+1$ at zero and $-1$ elsewhere, and $R_F$ diagonal $-1$ on true inputs and $+1$ otherwise. The input incumbent receives uniform weight $2^{-n}$, fuel is exactly $T+1$, and all natural subtractions are truncated. For $T=0$ the output is $(l,0,0)$ with uniform incumbent; $n=0$ has only the empty incumbent, and no bound on $f$ or positivity assumption on $b,T$ is imposed.
--
--   ## QAlgorithms.Nannicini.minFindRepeatProb
--
--   For any natural number $n$, integer-valued function $f$ on $n$-bit strings, natural parameters $b,T,k$, and arbitrary predicate $E$ on indexed $k$-tuples of triples in $\{0,1\}^n\times\mathbb N\times\mathbb N$, this is $\sum'_{(o_i)_{i<k}}\mathbf1\{E((o_i))\}\prod_{i<k}W(o_i)$ in nonnegative extended reals. Here $W$ is the output weight of this procedure: choose the initial incumbent $l$ with weight $2^{-n}$, start counters $q=g=0$ and fuel $T+1$, and repeatedly search for $F(j)=[f(j)<f(l)]$; a result $(a,c)$ within budget $q+c\leq T$ updates $q$ to $q+c$, updates $l$ to $k'$ only when $a=\mathrm{some}(k')$ and $f(k')<f(l)$, adds $G(L_n,c)+s$ to $g$, and uses one unit of fuel; an over-budget result terminates with $(l,T,g+G(L_n,T-q))$; zero fuel terminates with $(l,q,g)$. Define $s=3n+2b+1$, $h(m)=m+\lfloor m(m+1)/2\rfloor$, $L_n=[1,1,\ldots,n-1,n-1]$ (empty for $n\leq1$), and $G(L,0)=0$, $G([],c)=cs$ for positive $c$, while $G(m::L,c)=h(m)+cs$ for $0<c\leq2^m$ and $h(m)+2^ms+G(L,c-2^m)$ otherwise. The search distribution traverses $L_n$ starting with cost $0$: each head $m$ draws $j$ with weight $\sum_a|\chi_m(a,j)|^2$ and adds $2^m$, returns $\mathrm{some}(j)$ when $F(j)$ is true and continues otherwise; at the empty list it returns the true input of least binary value $B(j)=\sum_{i<n}[j_i]2^{n-1-i}$ with added cost $B(j)+1$, or none with added cost $2^n$. Here $\chi_m=(Q_m^*\otimes I)D_m(H_nR_0H_n^*R_F)(Q_m\otimes I)(|0^m\rangle\otimes H_n|0^n\rangle)$, $Q_m(a,a')=2^{-m/2}e^{2\pi iB(a)B(a')/2^m}$, $D_m(A)$ applies $A^{B(a)}$ on the second register with first register fixed, $H_n(y,z)=2^{-n/2}(-1)^{\sum_i y_iz_i}$, $R_0$ is diagonal $+1$ at zero and $-1$ elsewhere, and $R_F$ is diagonal $-1$ on true inputs and $+1$ otherwise. Every possible triple is included in the countable sum, without restrictions on output counters; subtraction is truncated on naturals. When $k=0$ there is exactly one empty tuple and the product is $1$, so the value is $1$ or $0$ according as $E$ holds on that empty tuple; $n,b,T$ may also be $0$.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Nannicini/Ch04c.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
/-!
# Nannicini, Chapter 4 (part c): searching when the number of marked items is not known

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages): Lemma 4.28 (p.92), Theorem 4.29 (p.93), Corollary 4.30 (p.94), and Theorem 4.31
(quantum minimum finding, p.96) in a corrected form with an explicit bit width, interruption rule
and gate-cost model (see its docstring).

Setting of §4.3.6 (p.91): the setting of §4.2 with `S = H^{⊗n}` (Rem. 4.13) and the phase
reflection `R|j⟩ = (−1)^{f(j)}|j⟩` built from `U_f : |j⟩|y⟩ ↦ |j⟩|y ⊕ f(j)⟩` (p.69), so that
`S|0⟩ = sin θ |ψ_G⟩ + cos θ |ψ_B⟩` with `sin θ = √(|M|/2^n)`, `M = {j : f(j) = 1}`; this `θ` is
the frozen `groverAngle |M| 2^n`. The output states of the amplitude estimation circuit
(Fig. 4.9) on the eigenstates `|ϕ±⟩` are `|ϑ±⟩ = Q_m† (2^{−m/2} Σ_k e^{±2iθk}|k⟩)` (p.92), the
frozen `aeVartheta m (±θ)`. Algorithm 1 (p.94) is the frozen `searchAlg1Weight f` (joint law of
the output, `none` = "no solution", and of the number of applications of `U_f`), with expected
cost `searchAlg1ExpectedCost f`: a round with `m` qubits of precision costs `2^m − 1`
applications of the Grover operator (one `U_f` each) plus one test of `f(j)`, and the final
enumeration costs one application per string tested.
-/

namespace QAlgorithms.Nannicini

open scoped ENNReal




/-- Quantum minimum finding (§4.4.1, Algorithm 2 and Theorem 4.31, pp.95–97).

Cost model (chunk-local; the source fixes none). `f : {0,1}^n → ℤ` takes values of bit width `b`
(`|f(j)| < 2^b`), and `U_f` writes `f(j)` in binary (p.95). Every application of the marking
unitary `U_m : |j⟩|y⟩ ↦ |j⟩|y ⊕ I(f(j) < f(ℓ))⟩` (Alg. 2, line 3) counts as one application of
`U_f`, as in the proof (p.97: "a single call to `U_f` plus some binary arithmetic operations"),
and is charged `mfStepGates n b = 3n + 2b + 1` additional gates: `S = H^{⊗n}`, `S†` and the
reflection `F` about `|0⟩` at `n` gates each, a `b`-bit comparison with `f(ℓ)` and its
uncomputation at `b` gates each, and one gate of control overhead. A round of Alg. 1 with `m`
qubits of precision is moreover charged `m + m(m+1)/2` gates (the `m` Hadamards and the inverse
QFT `Q_m†`: `m` Hadamards and `m(m−1)/2` controlled rotations). Only the asymptotic form of these
counts (`Θ(n + b)` per query, `Θ(m²)` per round) matters for the theorem.

This definition: gates charged, besides the call to `U_f`, for one application of the marking
unitary `U_m` of Alg. 2 inside a Grover iterate `S F S† R` (or for one test of a string):
`3n + 2b + 1` (Nannicini p.94–97). -/
def mfStepGates (n b : ℕ) : ℕ :=
  3 * n + 2 * b + 1

/-- Fixed gate overhead of one round of Alg. 1 (p.94) with `m` qubits of precision: `m`
Hadamards on the first register and the inverse QFT `Q_m†` counted as `m(m+1)/2` gates. -/
def mfRoundOverhead (m : ℕ) : ℕ :=
  m + m * (m + 1) / 2

/-- The precisions of the rounds of Alg. 1 (p.94): `m = 1, 1, 2, 2, …, n−1, n−1` (two rounds for
each `m < n`); this is the list used by the frozen `searchAlg1Weight`. -/
def alg1RoundList (n : ℕ) : List ℕ :=
  (List.range (n - 1)).flatMap fun i => [i + 1, i + 1]

/-- Additional gates performed by Alg. 1 (p.94) by the time it has made `c` applications of the
marking unitary, when its remaining rounds have precisions `rounds`. A round with `m` qubits
makes `2^m` applications (`2^m − 1` Grover iterates and one test of the measured string, as in
the frozen `searchAlg1Rounds`); a round that is entered is charged its full overhead
`mfRoundOverhead m`; after the rounds, every enumerated string costs one application. Since the
round costs are fixed, the number `c` of applications made so far determines the position in the
run, so this is both the gate count of a completed call of cost `c` and of a call interrupted
after `c` applications. -/
def alg1Gates (n b : ℕ) : List ℕ → ℕ → ℕ
  | _, 0 => 0
  | [], c => c * mfStepGates n b
  | m :: rest, c =>
      if c ≤ 2 ^ m then mfRoundOverhead m + c * mfStepGates n b
      else mfRoundOverhead m + 2 ^ m * mfStepGates n b + alg1Gates n b rest (c - 2 ^ m)

/-- The main loop of Alg. 2 (Nannicini p.96) with budget `T` applications of `U_f`, as a
weight on final triples `(ℓ, applications of U_f, additional gates)`. Arguments: remaining
fuel, incumbent `ℓ`, applications `q` and gates `g` used so far, and the outcome.

Each iteration runs Alg. 1 (the frozen `searchAlg1Weight`) with the marking function
`j ↦ I(f(j) < f(ℓ))`, whose outcome `(k, c)` (returned index or "no solution", applications of
the marking unitary) has the frozen weight. If the call completes within the budget
(`q + c ≤ T`), the incumbent becomes `k` when `f(k) < f(ℓ)` (line 5, charged `mfStepGates n b`
gates) and the loop continues. Otherwise the call is **interrupted** as soon as the `T`-th
application of `U_f` has been made (the reading of "while the number of evaluations of `U_f` does
not exceed `T`" that the `O(√2^n log 1/δ)` total needs), its result is discarded and Alg. 2
returns `ℓ`, having used exactly `T` applications and `alg1Gates … (T − q)` gates for that call.
Every call makes at least one application, so fuel `T + 1` reaches an interruption on every
path; the fuel-`0` clause is never reached from `minFindWeight`. -/
noncomputable def minFindLoop {n : ℕ} (f : Qubits n → ℤ) (b T : ℕ) :
    ℕ → Qubits n → ℕ → ℕ → Qubits n × ℕ × ℕ → ℝ≥0∞
  | 0, l, q, g, out => if out = (l, q, g) then 1 else 0
  | fuel + 1, l, q, g, out =>
      ∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight (fun j => decide (f j < f l)) oc *
        (if q + oc.2 ≤ T then
          minFindLoop f b T fuel
            (match oc.1 with
              | some k => if f k < f l then k else l
              | none => l)
            (q + oc.2) (g + alg1Gates n b (alg1RoundList n) oc.2 + mfStepGates n b) out
        else if out = (l, T, g + alg1Gates n b (alg1RoundList n) (T - q)) then 1 else 0)

/-- One run of Alg. 2 (Nannicini p.96) with budget `T`: the initial incumbent `ℓ` is uniform on
`{0,1}^n` (line 1); weight of the final triple `(returned ℓ, applications of U_f, additional
gates)`. -/
noncomputable def minFindWeight {n : ℕ} (f : Qubits n → ℤ) (b T : ℕ)
    (out : Qubits n × ℕ × ℕ) : ℝ≥0∞ :=
  ∑ l : Qubits n, ((2 : ℝ≥0∞) ^ n)⁻¹ * minFindLoop f b T (T + 1) l 0 0 out

/-- Probability of an event `E` about the outcomes of `k` independent runs of Alg. 2 with budget
`T` (the repetition in the proof of Theorem 4.31, p.97). -/
noncomputable def minFindRepeatProb {n : ℕ} (f : Qubits n → ℤ) (b T k : ℕ)
    (E : (Fin k → Qubits n × ℕ × ℕ) → Prop) : ℝ≥0∞ :=
  open Classical in
  ∑' outs : Fin k → Qubits n × ℕ × ℕ, if E outs then ∏ i, minFindWeight f b T (outs i) else 0


end QAlgorithms.Nannicini


