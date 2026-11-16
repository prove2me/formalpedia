-- Prove2me | Definitions.Def_SubspaceEvasion312_Explicit_Supplement_codes
-- name    : SubspaceEvasion312_Explicit_Supplement_codes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:46:02.238933+00:00
-- url     : https://prove2.me/theorems/31968185-8ce6-4163-aaf8-25945915b7fa
-- title:
--   Standard and dimension list recovery, nonlinear rate, constructable sets
-- statement:
--   Let $F=\mathbb F_q$ be a finite field, $V_n=F^n$ and $W_{s,m}=(F^s)^m$, with block Hamming distance $\mathrm{Ham}(c,y)=|\{i:c_i\neq y_i\}|$, as in the mission's published algebra definitions.
--
--   1. **Recovered list.** For a set of words $C\subseteq W_{s,m}$ (not necessarily additive), input lists $S_1,\dots,S_m\subseteq F^s$ and a radius $\rho$, the recovered list is
--   $$\mathcal L(C,S,\rho)=\{c\in C:\exists\,y\in S_1\times\cdots\times S_m,\ \mathrm{Ham}(c,y)\le\rho m\}.$$
--   2. **Standard list recovery.** $C$ is $(\rho,\ell,L)$ list-recoverable when $|\mathcal L(C,S,\rho)|\le L$ for all lists with $|S_i|\le\ell$. It is stated as: every finite subset of the recovered list has at most $L$ elements, so an infinite list never satisfies the bound.
--   3. **Dimension list recovery (Definition 27).** An additive code $C$ is $(\rho,\ell,r)$ dimension list-recoverable when, for all lists with $|S_i|\le\ell$, the recovered list $\mathcal L(C,S,\rho)$ lies in some $F$-linear subspace of $W_{s,m}$ of dimension at most $r$.
--   4. **Rate of a set of words.** $\mathrm{rate}(C)=\log_q|C|/(sm)=\log_{q^s}|C|/m$.
--   5. **Constructable and encodable sets (printed p. 7).** Fix an ordering of $F$. The $d$ base-$q$ digits (least significant first) of an integer $i$ form a vector in $F^d$. A finite set $A\subseteq F^k$ is constructable in time $T$ by a register program $P$ when there are $d$ with $|A|\le q^d$ and a bijection $e:\{0,\dots,|A|-1\}\to A$ such that, for every index $i$, $P$ run on the digits of $i$ (plus fixed natural parameters) outputs $e(i)$ within charged time $T$ and word bound $B$. A set of words $C\subseteq W_{s,m}$ is encodable in time $T$ in the same way, with output the codeword.
--   6. **Theorem 25's list bound.** $\ell_A=\lceil 50r^2/\varepsilon\rceil$, $\ell_B=\lceil 256r(1+\log_2(r/\varepsilon))/\varepsilon\rceil$ and $L(r,\varepsilon)=\min(2\ell_A,2\ell_B)$.
--
--   These objects state Theorems 25, 28, 32 and 33: the subcode $\mathrm{Enc}(A)$ is a nonlinear code, whose list recovery, rate and encoding are not covered by the additive notions of the base mission.
--
--   **Formalization Note** Indices start at $0$ rather than $1$; the time model is the mission's published register machine, in which program size and every step are charged.
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, Explicit Subspace Evasive Sets via Subspace Designs, STOC 2027 submission #312 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf, PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc, standard list recovery printed p. 2 (PDF p. 3); encoder, constructable and membership conventions printed p. 7 (PDF p. 8); Definition 27 printed p. 14 (PDF p. 15); rate of Enc(A) and Theorem 25's parameters printed pp. 13–14 (PDF pp. 14–15)

import Definitions.Def_SubspaceEvasion312_Explicit_construction

noncomputable section

namespace SubspaceEvasion312.Explicit.Supplement
open scoped BigOperators

/-- The words of a (not necessarily additive) code within block Hamming distance
rho * m of some word of the product list S_1 x ... x S_m. -/
def listRecovered {F : Type} {s m : ℕ} (C : Set (Blocks F s m))
    (S : Fin m → Finset (Vec F s)) (ρ : ℝ) : Set (Blocks F s m) :=
  {c | c ∈ C ∧ ∃ y : Blocks F s m, (∀ i, y i ∈ S i) ∧ (hamming c y : ℝ) ≤ ρ * m}

/-- Standard (rho, ell, L) list recovery (printed p. 2), for any set of words.
Every finite subset of the list is bounded, so an infinite list never passes. -/
def SetListRecoverable {F : Type} {s m : ℕ} (C : Set (Blocks F s m))
    (ρ : ℝ) (ℓ L : ℕ) : Prop :=
  ∀ S : Fin m → Finset (Vec F s), (∀ i, (S i).card ≤ ℓ) →
    ∀ T : Finset (Blocks F s m), (↑T : Set (Blocks F s m)) ⊆ listRecovered C S ρ →
      T.card ≤ L

/-- Definition 27: every recovered list lies in a subspace of dimension at most r. -/
def DimensionListRecoverable {F : Type} [Field F] {s m : ℕ} (C : Code F s m)
    (ρ : ℝ) (ℓ r : ℕ) : Prop :=
  ∀ S : Fin m → Finset (Vec F s), (∀ i, (S i).card ≤ ℓ) →
    ∃ U : Submodule F (Blocks F s m), Module.finrank F U ≤ r ∧
      listRecovered (C : Set (Blocks F s m)) S ρ ⊆ (U : Set (Blocks F s m))

/-- Rate log_q |C| / (s m) of a not necessarily additive code over F_q^s. -/
def setRate {F : Type} [Fintype F] {s m : ℕ} (C : Set (Blocks F s m)) : ℝ :=
  Real.logb (Fintype.card F) (C.ncard : ℝ) / ((s * m : ℕ) : ℝ)

/-- The d least-significant-first base-q digits of the integer i, as field symbols. -/
def digitVector {F : Type} [Field F] [Fintype F]
    (alphabet : Fin (Fintype.card F) ≃ F) (d i : ℕ) : Vec F d :=
  fun j => alphabet ⟨(i / (Fintype.card F) ^ j.val) % Fintype.card F,
    Nat.mod_lt _ Fintype.card_pos⟩

/-- Printed p. 7: A is constructable in time T when one program computes a bijection
from the indices {0, ..., |A|-1}, given as d base-q digits with q^d >= |A|, onto A.
All preprocessing happens inside every charged run. -/
def Constructable {F : Type} [Field F] [Fintype F] {k : ℕ} (A : Set (Vec F k))
    (alphabet : Fin (Fintype.card F) ≃ F) (P : Program F) (params : List ℕ)
    (T B : ℕ) : Prop :=
  A.Finite ∧ ∃ (d : ℕ) (e : Fin A.ncard ≃ A), A.ncard ≤ (Fintype.card F) ^ d ∧
    ∀ i : Fin A.ncard, RunsWithin P params (vectorData (digitVector alphabet d i.val))
      T B (vectorData (e i).val)

/-- A not necessarily additive code is encodable in time T when one program maps
each index (base-q digits) to its codeword, through a bijection onto the code. -/
def EncodableSet {F : Type} [Field F] [Fintype F] {s m : ℕ} (C : Set (Blocks F s m))
    (alphabet : Fin (Fintype.card F) ≃ F) (P : Program F) (params : List ℕ)
    (T B : ℕ) : Prop :=
  C.Finite ∧ ∃ (d : ℕ) (e : Fin C.ncard ≃ C), C.ncard ≤ (Fintype.card F) ^ d ∧
    ∀ i : Fin C.ncard, RunsWithin P params (vectorData (digitVector alphabet d i.val))
      T B (blockData (e i).val)

/-- Theorem 25's proof: ell = ceil(50 r^2 / eps) in Case A (Corollary 21). -/
def polyQuadraticList (r : ℕ) (ε : ℝ) : ℕ := ⌈50 * (r : ℝ) ^ 2 / ε⌉₊

/-- Theorem 25's list bound L = 2 ell, the better of Case A and Case B
(Case B: ell = ceil(256 r (1 + log2(r/eps)) / eps), the published logarithmicList). -/
def polyFieldBound (r : ℕ) (ε : ℝ) : ℕ :=
  min (2 * polyQuadraticList r ε) (2 * logarithmicList r ε)

end SubspaceEvasion312.Explicit.Supplement


