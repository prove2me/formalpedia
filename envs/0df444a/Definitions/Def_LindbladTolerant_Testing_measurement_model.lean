-- Prove2me | Definitions.Def_LindbladTolerant_Testing_measurement_model
-- name    : LindbladTolerant_Testing_measurement_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:57:21.824892+00:00
-- url     : https://prove2.me/theorems/d32e3151-b213-4b5b-b123-f7175f667b9f
-- title:
--   Pauli discovery, product records, and the ordered-pair estimator
-- statement:
--   Let $\sigma$ be an SR density matrix and $\sigma_R$ its reference marginal. Measuring a fresh copy in the normalized Pauli-vector basis gives label $Q$ with probability $\langle\!\langle Q|\sigma|Q\rangle\!\rangle$. For $m$ independent labels $Q_1,\ldots,Q_m$, form the candidate set $\mathcal C$ of nonidentity strings $P$ of weight at most $k$ whose supports lie in $\operatorname{supp}(Q_i)\cup\operatorname{supp}(Q_j)$ for some $i,j$, allowing $i=j$. Put
--   $$a_P=\operatorname{Tr}(P\sigma_R),\qquad G=\sum_{P\ne I}a_P^2,\qquad G_{\mathcal C}=\sum_{P\in\mathcal C}a_P^2.$$
--   On each fresh reference marginal, independently choose a uniform axis from $X,Y,Z$ on each discovered site and measure its sign. A record has
--   $$X_P=3^{\mathrm{wt}(P)}\prod_{i\in\operatorname{supp}(P)}b_i$$
--   when all measured axes match $P$, and zero otherwise. For $N$ fresh records define
--   $$\widehat G=\frac{\sum_{r\ne s}\sum_{P\in\mathcal C}X_{r,P}X_{s,P}}{N(N-1)}.$$
--   The pairs are ordered. The same record supplies all its entries, so those entries are not declared independent. An empty candidate set gives zero. Conditional means and variances are finite sums under the fresh records' Born law, at a fixed first-batch history.
--
--   The SWAP measurement acts on two full SR copies and uses the effects $(I\pm\mathrm{SWAP})/2$. Its probabilities are computed from those effects and $\sigma\otimes\sigma$.
--
--   **Formalization Note** Unmeasured sites have fixed dummy record entries; their measurement effect is the identity. No measurements or independent outcomes are introduced there. The $N\ge2$ domain is imposed by the estimator theorems.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, §§4.1–4.2, pp.18–23, PDF pp.18–23, Eqs.(47)–(49),(67), SWAP measurement p.23

import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open scoped BigOperators ComplexConjugate Matrix

namespace LindbladTolerant.Testing

attribute [local instance] Classical.propDecidable Classical.decEq
variable {n m N : ℕ}

/-- Exact Born probabilities in the normalized Pauli-vector basis. -/
def bellWeight (sigma : Op (Qubits n × Qubits n)) (p : Pauli n) : ℝ :=
  (outer (ket (pauliMatrix p)) (ket (pauliMatrix p)) * sigma).trace.re

def discoveryWeight (sigma : Op (Qubits n × Qubits n)) (q : Fin m → Pauli n) : ℝ :=
  ∏ j, bellWeight sigma (q j)

def candidateSet (k : ℕ) (q : Fin m → Pauli n) : Finset (Pauli n) :=
  Finset.univ.filter (fun p => p ≠ 0 ∧ weight p ≤ k ∧
    ∃ i j : Fin m, support p ⊆ support (q i) ∪ support (q j))

def discoveredSupport (q : Fin m → Pauli n) : Finset (Fin n) :=
  Finset.univ.biUnion (fun i => support (q i))

def marginalCoefficient (sigma : Op (Qubits n × Qubits n)) (p : Pauli n) : ℝ :=
  (pauliMatrix p * traceSystem sigma).trace.re

def marginalG (sigma : Op (Qubits n × Qubits n)) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Pauli n)).erase 0, (marginalCoefficient sigma p)^2

def candidateG (sigma : Op (Qubits n × Qubits n)) (c : Finset (Pauli n)) : ℝ :=
  ∑ p ∈ c, (marginalCoefficient sigma p)^2

/-- Product-Pauli choices and signs. Outside the measured support these are dummy
zero entries, forced by recordWeight, and carry no additional measurement. -/
abbrev ProductRecord (n : ℕ) := (Fin n → Fin 3) × (Fin n → Bool)

def sign (b : Bool) : ℝ := if b then -1 else 1

def recordEffect (s : Finset (Fin n)) (r : ProductRecord n) : Op (Qubits n) :=
  fun x y => ∏ i,
    if i ∈ s then ((if x i = y i then 1 else 0) +
      (sign (r.2 i) : ℂ) * onePauli ⟨(r.1 i).val+1, by omega⟩ (x i) (y i)) / 2
    else if x i = y i then 1 else 0

def recordWeight (sigma : Op (Qubits n × Qubits n)) (s : Finset (Fin n))
    (r : ProductRecord n) : ℝ :=
  if ∀ i, i ∉ s → r.1 i = 0 ∧ r.2 i = false then
    (3 : ℝ)^(-(s.card : ℤ)) * (recordEffect s r * traceSystem sigma).trace.re
  else 0

def recordEntry (r : ProductRecord n) (p : Pauli n) : ℝ :=
  if ∀ i ∈ support p, (r.1 i).val + 1 = (p i).val then
    (3 : ℝ)^(weight p) * ∏ i ∈ support p, sign (r.2 i)
  else 0

/-- Ordered distinct pairs; no independence is imposed between entries of one record. -/
def uStatistic (c : Finset (Pauli n)) (records : Fin N → ProductRecord n) : ℝ :=
  (∑ r, ∑ s, if r ≠ s then
    ∑ p ∈ c, recordEntry (records r) p * recordEntry (records s) p else 0) /
      ((N : ℝ) * ((N : ℝ)-1))

def recordsWeight (sigma : Op (Qubits n × Qubits n)) (s : Finset (Fin n))
    (records : Fin N → ProductRecord n) : ℝ := ∏ r, recordWeight sigma s (records r)

def conditionalMean (sigma : Op (Qubits n × Qubits n)) (k : ℕ)
    (q : Fin m → Pauli n) (N : ℕ) : ℝ :=
  ∑ r : Fin N → ProductRecord n,
    recordsWeight sigma (discoveredSupport q) r * uStatistic (candidateSet k q) r

def conditionalVariance (sigma : Op (Qubits n × Qubits n)) (k : ℕ)
    (q : Fin m → Pauli n) (N : ℕ) : ℝ :=
  ∑ r : Fin N → ProductRecord n,
    recordsWeight sigma (discoveredSupport q) r *
      (uStatistic (candidateSet k q) r - conditionalMean sigma k q N)^2

/-- The SWAP exchanges the full SR registers of two fresh copies. -/
def swapMatrix {I : Type*} [DecidableEq I] : Op (I × I) :=
  fun i j => if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0

def swapWeight (sigma : Op (Qubits n × Qubits n)) (b : Bool) : ℝ :=
  (((1/2 : ℂ) • (1 + (sign b : ℂ) • swapMatrix)) *
    Matrix.kronecker sigma sigma).trace.re

end LindbladTolerant.Testing


