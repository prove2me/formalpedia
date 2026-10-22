-- Prove2me | Definitions.Def_OptimalQueuingComplexity_Network_Instance
-- name    : OptimalQueuingComplexity_Network_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T09:31:02.944273+00:00
-- url     : https://prove2.me/theorems/5ca0aeee-6c02-4e08-a585-8974a75381be
-- title:
--   Instance of NETWORK OF QUEUES, its encoding and well-formedness (Section 2)
-- statement:
--   An instance of NETWORK OF QUEUES consists of a finite set $C = \{0, \dots, n_C - 1\}$ of customer classes and a finite set $S = \{0, \dots, n_S - 1\}$ of servers, together with
--   * the server $\sigma(c) \in S$ that is the only one able to serve class $c$;
--   * the mean service time $\mu(c) \in \mathbb{Q}$ and the weight $w(c) \in \mathbb{Q}$ of each class;
--   * a partition $C = D \sqcup R$ (for each class, whether it lies in $D$);
--   * a set $N(c) \subseteq C$ for each $c \in D$ (represented by a Boolean matrix, read only on rows $c \in D$);
--   * rational routing probabilities $p_{cc'}$ (read only on rows $c \in R$);
--   * the initial number $n_i(c) \in \mathbb{N}$ of class-$c$ customers **waiting** (not in service) at time $0$;
--   * the set $S_0$ of servers busy at time $0$ and the class $c_s$ served by each $s \in S_0$;
--   * a rational threshold $K$.
--
--   The instance is encoded as the concatenation of the length-faithful encodings of $n_C$, $n_S$ and all these tables (counts in binary, rationals as numerator/denominator pairs).
--
--   An instance is **well formed** if
--   $$\sigma(c_s) = s \ (s \in S_0),\quad \mu(c) \ge 0,\quad p_{cc'} \ge 0,\ \textstyle\sum_{c'} p_{cc'} = 1\ (c \in R),\quad N(c) \ne \emptyset\ (c \in D),$$
--   and there is no cycle $c_1 \to c_2 \to \dots \to c_1$ of the routing graph ($c \to c'$ iff $c \in D, c' \in N(c)$, or $c \in R, p_{cc'} > 0$) all of whose classes have $\mu = 0$.
--
--   **Formalization Note.** Nonnegative means, probability vectors and $\sigma(c_s) = s$ are implicit in the paper. Nonempty $N(c)$ is not stated in the paper, but without it no routing decision exists. The ban on zero-mean routing cycles is an added convention: $\mu(c) = 0$ means instantaneous service, and such a cycle would let a customer complete infinitely many services at one instant. All clauses are checkable in polynomial time.
-- source:
--   Papadimitriou & Tsitsiklis, The Complexity of Optimal Queuing Network Control, Math. Oper. Res. 24(2) (1999), pp. 294–295, Section 2 (definition of a network of queues and of an instance of NETWORK OF QUEUES)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Network_encNat

namespace OptimalQueuingComplexity.Network

/-- An instance of **NETWORK OF QUEUES** (Papadimitriou & Tsitsiklis 1999, Section 2, p. 295):
"the finite sets `C`, `S`, the function `σ : C ↦ S`, rational-valued functions `μ` and `w`
defined on `C`, subsets `D` and `R` of `C`, a set `N(c) ⊆ C` for each `c ∈ D`, rational
coefficients `p_{cc'}` for every `c ∈ R` and `c' ∈ C`, the initial numbers `n_i(c)` of customers
of each class, the set `S₀` of busy servers at time zero, the class `c_s` of the customer being
served at time zero by each server `s ∈ S₀`, and a rational number `K`."

* The customer classes are `C = Fin nC` and the servers are `S = Fin nS`.
* `server c = σ(c)`, `mean c = μ(c)` (mean service time), `weight c = w(c)`.
* `inD c = true` iff `c ∈ D`; the partition `C = D ⊔ R` is built in (`R` = the classes with
  `inD c = false`).
* `next c c' = true` iff `c' ∈ N(c)`; it is only read for `c ∈ D`.
* `prob c c' = p_{cc'}`; it is only read for `c ∈ R`.
* `init c = n_i(c)` is the number of class-`c` customers **waiting** (not in service) at time 0;
  the customers in service at time 0 are described by `busy0` in addition.
* `busy0 s = none` iff `s ∉ S₀`, and `busy0 s = some c` iff `s ∈ S₀` and `c_s = c`.
* `K` is the threshold of the decision problem. -/
structure Instance where
  /-- number of customer classes; `C = Fin nC` -/
  nC : ℕ
  /-- number of servers; `S = Fin nS` -/
  nS : ℕ
  /-- `σ(c)`: the only server that can serve class `c` -/
  server : Fin nC → Fin nS
  /-- `μ(c)`: the mean (exponential) service time of class `c` -/
  mean : Fin nC → ℚ
  /-- `w(c)`: the weight of a class-`c` service completion -/
  weight : Fin nC → ℚ
  /-- `true` iff `c ∈ D` (routing chosen by the controller); `false` iff `c ∈ R` -/
  inD : Fin nC → Bool
  /-- `next c c' = true` iff `c' ∈ N(c)` (read for `c ∈ D` only) -/
  next : Fin nC → Fin nC → Bool
  /-- `p_{cc'}` (read for `c ∈ R` only) -/
  prob : Fin nC → Fin nC → ℚ
  /-- `n_i(c)`: class-`c` customers waiting at time 0 -/
  init : Fin nC → ℕ
  /-- `S₀` and `c_s`: `busy0 s = some c_s` for `s ∈ S₀`, `none` otherwise -/
  busy0 : Fin nS → Option (Fin nC)
  /-- the threshold `K` -/
  K : ℚ

/-- The binary encoding of an instance: the concatenation of the self-delimiting encodings
(`encNat`, `encRat`, …) of `nC`, `nS`, and then of every table in field order (`server`,
`mean`, `weight`, `inD`, `next` row by row, `prob` row by row, `init`, `busy0`) and finally `K`.
All naturals (including the customer counts `init c`) are written in binary and all rationals as
(numerator, denominator) pairs, so the length of the encoding is polynomial in the bit size of
the instance and conversely. -/
def Instance.enc (I : Instance) : List Bool :=
  encNat I.nC ++ encNat I.nS ++ encTable encFin I.server ++ encTable encRat I.mean ++
    encTable encRat I.weight ++ encTable encBool I.inD ++ encTable (encTable encBool) I.next ++
    encTable (encTable encRat) I.prob ++ encTable encNat I.init ++
    encTable (encOption encFin) I.busy0 ++ encRat I.K

/-- The routing graph: `c → c'` if a class-`c` customer can become a class-`c'` customer on
completing service, i.e. `c ∈ D` and `c' ∈ N(c)`, or `c ∈ R` and `p_{cc'} > 0`. -/
def Instance.edge (I : Instance) (c c' : Fin I.nC) : Prop :=
  (I.inD c = true ∧ I.next c c' = true) ∨ (I.inD c = false ∧ 0 < I.prob c c')

/-- The routing graph restricted to classes of zero mean service time. -/
def Instance.zeroEdge (I : Instance) (c c' : Fin I.nC) : Prop :=
  I.mean c = 0 ∧ I.mean c' = 0 ∧ I.edge c c'

/-- Well-formedness of an instance (all clauses are checkable in polynomial time):
* every server busy at time 0 serves a customer of one of its own classes (`σ(c_s) = s`);
* mean service times are nonnegative (`μ(c) = 0` is allowed and means instantaneous service);
* for `c ∈ R`, `(p_{cc'})_{c'}` is a probability vector;
* for `c ∈ D`, `N(c)` is nonempty (otherwise no routing decision exists);
* **added convention**: there is no routing cycle all of whose classes have zero mean service
  time (otherwise a customer could complete infinitely many services at a single instant and
  the throughput would be infinite). -/
structure Instance.WellFormed (I : Instance) : Prop where
  busy0_server : ∀ s c, I.busy0 s = some c → I.server c = s
  mean_nonneg : ∀ c, 0 ≤ I.mean c
  prob_nonneg : ∀ c c', I.inD c = false → 0 ≤ I.prob c c'
  prob_sum : ∀ c, I.inD c = false → ∑ c', I.prob c c' = 1
  next_nonempty : ∀ c, I.inD c = true → ∃ c', I.next c c' = true
  no_zero_cycle : ∀ c, ¬ Relation.TransGen I.zeroEdge c c

end OptimalQueuingComplexity.Network


