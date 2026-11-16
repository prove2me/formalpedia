-- Prove2me | Definitions.Def_GabidulinProx_UniqueDecoding_Supplement_Objects
-- name    : GabidulinProx_UniqueDecoding_Supplement_Objects
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:40:40.509062+00:00
-- url     : https://prove2.me/theorems/71cc1767-e4bb-4bb4-ba78-5e9a06b8cf79
-- title:
--   Minimum rank distance, interleaved distance, the parameter set $H$ and IOPP acceptance
-- statement:
--   Let $L/K$ be an extension of finite fields, $q=|K|$, and let $C\le L^n$ be an $L$-linear code. The rank of $y\in L^n$ is the $K$-dimension of the span of its coordinates (published `wordRank`).
--
--   1. **Minimum rank distance.** $d(C)=\min\{\operatorname{rk}_K(c):c\in C,\ c\ne0\}$ (Definitions 2.3–2.4, p. 13). For the zero code the set is empty and the value is $0$.
--   2. **Interleaved distance.** For $U\in L^{n\times s}$ (row $r$ is $U(r)\in L^s$), $d(U^T,C^s)$ is the minimum over $c_1,\dots,c_s\in C$ of the $K$-dimension of the span of the $n$ columns $\bigl(U_{r,j}-c_{j,r}\bigr)_{j<s}\in L^s$, i.e. the rank of the $ms\times n$ expansion of $U^T-[c_1;\dots;c_s]$ (Definition 2.5, p. 13). It is a finite nonempty minimum; for $s=2$ it agrees with the published pair distance.
--   3. **The parameter set $H$** of §3.4 (p. 28): for intermediate fields $K\subseteq\mathbb F_Q\subseteq E$ and an $\mathbb F_Q$-subspace $V\subseteq E$ of dimension $c$,
--   $$H=\{-A_W(x)^{q-1}:W\le V,\ \dim_{\mathbb F_Q}W=c-1,\ x\in V\setminus W\},$$
--   with $A_W=\prod_{w\in W}(X-w)$ the published subspace annihilator.
--   4. **IOPP acceptance probability** (protocol box, p. 30): for an oracle $U\in L^{n\times s}$, a number of queries $t$ and a prover strategy $P:L^s\to L^n$,
--   $$\Pr_{a,J}\bigl[P(a)\in C\ \wedge\ \forall j\in J,\ P(a)_j=\textstyle\sum_i a_iU_{j,i}\bigr],$$
--   with $a$ uniform in $L^s$ and $J$ a uniform $t$-element subset of the $n$ positions, computed as a count divided by $|L|^s\binom nt$.
--
--   These objects are used by the supplement's statements about general linear codes (Lemma 3.1, Theorems 1.2, 3.2), the code parameters in Theorems 1.4, 1.5, 3.15, the construction of §3.4 and the proximity test of §4.1.
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Definitions 2.3–2.5 p.13; §3.4 p.28; §4.1 protocol box p.30. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf

import Definitions.Def_GabidulinProx_UniqueDecoding_Codes

open scoped BigOperators

namespace GabidulinProx.UniqueDecoding.Supplement

open GabidulinProx.UniqueDecoding

/-- Definitions 2.3–2.4, p.13: the minimum rank distance of a linear code, the least `K`-rank
of a nonzero codeword. For the zero code the set is empty and the value is `0`; every theorem
using it then has an unsatisfiable hypothesis or a conclusion that refutes `C = ⊥`. -/
noncomputable def minRankDistance (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (C : Submodule L (Fin n → L)) : ℕ :=
  sInf {r : ℕ | ∃ c ∈ C, c ≠ 0 ∧ wordRank K c = r}

/-- Definition 2.5, p.13, and §4.1, p.29: `d(Uᵀ, Cˢ)` for `U ∈ L^{n×s}` (row `r` is `U r`,
column `j` is `fun r => U r j`). It is the minimum, over `s`-tuples of codewords, of the
joint `K`-rank of the `n` columns `(U r j - c_j r)_j ∈ L^s` of the `s × n` matrix `Uᵀ - C`,
i.e. the `K`-rank of its `ms × n` expansion. A finite nonempty minimum. -/
noncomputable def interleavedDistance (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype L] {n s : ℕ} (C : Submodule L (Fin n → L))
    (U : Fin n → Fin s → L) : ℕ := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  exact (Finset.univ.image (fun c : Fin s → C =>
    wordRank K (fun r : Fin n => fun j : Fin s => U r j - (c j : Fin n → L) r))).min'
      (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- §3.4, p.28 (Lemma 3.14): the parameter set
`H = {-A_W(x)^(q-1) : W ⊆ V, dim_{F_Q} W = c - 1, x ∈ V \ W}`, where `q = |K|`, `F_Q = KQ`,
`c = dim_{KQ} V` and `A_W = ∏_{w∈W}(X - w)` is the subspace annihilator. -/
def paramSet (K KQ : Type*) {E : Type*} [Field K] [Fintype K] [Field KQ] [Field E]
    [Fintype E] [Algebra KQ E] (V : Submodule KQ E) : Set E :=
  {y | ∃ W : Submodule KQ E, W ≤ V ∧ Module.finrank KQ W = Module.finrank KQ V - 1 ∧
    ∃ x ∈ V, x ∉ W ∧ y = -((annihilator KQ W).eval x) ^ (Fintype.card K - 1)}

/-- The IOPP of §4.1 (box, p.30): the exact probability that the verifier accepts the oracle
`U` against a prover strategy `P` (the step-2 message as a function of the challenge `a`).
The challenge `a` is uniform in `L^s` and the query set `J` is a uniform `t`-element subset of
the `n` positions; the verifier accepts iff `P a ∈ C` and `(P a)_j = a · U(j)ᵀ` for `j ∈ J`. -/
noncomputable def acceptProb {L : Type*} [Field L] [Fintype L] {n s : ℕ}
    (C : Submodule L (Fin n → L)) (U : Fin n → Fin s → L) (t : ℕ)
    (P : (Fin s → L) → (Fin n → L)) : ℝ := by
  classical
  exact (((Finset.univ : Finset (Fin s → L)) ×ˢ
      (Finset.powersetCard t (Finset.univ : Finset (Fin n)))).filter
      (fun aJ => P aJ.1 ∈ C ∧ ∀ j ∈ aJ.2, P aJ.1 j = ∑ i, aJ.1 i * U j i)).card /
    ((Fintype.card L : ℝ) ^ s * (Nat.choose n t : ℝ))

end GabidulinProx.UniqueDecoding.Supplement


