-- Prove2me | Definitions.Def_RandModSubsetSum_Kernels
-- name    : RandModSubsetSum_Kernels
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:01:12.976659+00:00
-- url     : https://prove2.me/theorems/df4217f7-a540-4248-a073-705b645b41b6
-- title:
--   Nominal kernels, the entropy rates $D_j$, the observation entropies $E_{a,b}$, and the prescribed representation family $\mathcal D$
-- statement:
--   **Nominal kernels** (§3.1). $R^{(r)}_j((a,b)\mid c)$, $0\le j\le 6$, is the probability of the ordered child pair $(a,b)\in A_{j+1}^2$ given the parent symbol $c\in A_j$ in stratum $r$: nonnegative, supported on $a+b=c$, summing to one over the child pairs for each $c\in A_j$, and symmetric, $R((a,b)\mid c)=R((b,a)\mid c)$. *Positivity* means $R>0$ on every admissible cell (Appendix A).
--
--   **Derived distributions** (39). $P^{(r)}_0(1)=\rho_r$, $P^{(r)}_0(0)=1-\rho_r$, $\Gamma^{(r)}_j(a,b)=P^{(r)}_j(a+b)R^{(r)}_j((a,b)\mid a+b)$, $P^{(r)}_{j+1}(a)=\sum_b\Gamma^{(r)}_j(a,b)$. The rates are $H_j=\sum_rw_rH(P^{(r)}_j)$ and $D_j=\sum_rw_rH(R^{(r)}_j\mid P^{(r)}_j)$ with $H(R\mid P)=\sum_{c:P(c)>0}P(c)H(R(\cdot\mid c))$.
--
--   **Depth-two observations** ((9), (40)). For root symbol $c$,
--   $$\Gamma^{(r,c)}_{2,[4]}(u)=R^{(r)}_0((u_1+u_2,u_3+u_4)\mid c)\,R^{(r)}_1((u_1,u_2)\mid u_1+u_2)\,R^{(r)}_1((u_3,u_4)\mid u_3+u_4).$$
--   For a subspace $S=\mathrm{row}(B)\le\mathbb F_7^3$ and $g_B(u)=B(u_1,u_2,u_3)^{\mathsf T}\bmod 7$, the nominal observation entropy is
--   $$H(BV_{2,[3]}\bmod 7\mid X,J)=\sum_rw_r\sum_{c\in\{0,1\}}P^{(r)}_0(c)\,H\big(g_B(\Gamma^{(r,c)}_{2,[4]})\big),$$
--   and $b_1(B)=\dim(\mathrm{row}(B)\cap\langle e_{\rm sum}\rangle)$, $e_{\rm sum}=(1,1,0)$, $b_2(B)=\mathrm{rank}(B)-b_1(B)$. $E_{a,b}$ is the minimum over the $B$ of profile $(a,b)$.
--
--   **Exact types and the family $\mathcal D$** (§6.2, Algorithm 2). With $N^{\rm root}_{r,c}=|\{k\in I_r:x_k=c\}|$, the depth-two joint types are $\hat\Gamma^{(r,c)}_{2,[4]}=\lfloor\Gamma^{(r,c)}_{2,[4]}\rceil_{N^{\rm root}_{r,c}}$ (tuples ordered lexicographically); their projections give the slot types at depth two; for a parent slot $(j,v)$ with $j\ge2$ and prescribed count $N=N^{(r)}_{j,v}(c)>0$, $\hat R^{(r)}_{j,v}(\cdot\mid c)=\lfloor R^{(r)}_j(\cdot\mid c)\rceil_N$, and the child slot types are the marginals of the sibling types. $\mathcal D$ is the set of representations of $x$ that realize, on every stratum, the exact depth-two joint counts for each root symbol and the exact sibling counts at every slot of depth $2\le j\le6$.
--
--   **Formalization Note** The observation $g_B$ is written basis-free as the values $\langle s,u_{[3]}\rangle\bmod 7$ for $s\in S$; it determines and is determined by $Bu_{[3]}$, so its image entropy does not depend on the basis. Slot counts and child-pair counts are computed recursively from the prescription; slots are 0-indexed (left child even, right child odd).
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), §3.1, pp. 11–12; §4.1, (9), p. 22; §6.2, (39)–(40), pp. 44–45; Algorithm 2, p. 58; Appendix A, p. 55

import Mathlib
import Definitions.Def_RandModSubsetSum_Types
import Definitions.Def_RandModSubsetSum_Strata
import Definitions.Def_RandModSubsetSum_Template

open scoped BigOperators

namespace RandModSubsetSum

/-- A family of nominal decomposition kernels: `R j r c (a, b)` is `R_j^{(r)}((a, b) | c)`, the
probability of the ordered child pair `(a, b)` at depth `j + 1` given the parent symbol `c` at depth
`j`, in stratum `r` (§3.1, p. 11). Only `0 ≤ j ≤ 6` is used. -/
abbrev Kernel := ℕ → Fin 13 → ℤ → ℤ × ℤ → ℝ

/-- The ordered child pairs at parent depth `j`: `A_{j+1} × A_{j+1}`. -/
noncomputable def childPairs (j : ℕ) : Finset (ℤ × ℤ) := alph (j + 1) ×ˢ alph (j + 1)

/-- The conditions of §3.1 (p. 11) on nominal kernels, for `0 ≤ j ≤ 6`: nonnegative, supported on
`a + b = c` with `c ∈ A_j` and `a, b ∈ A_{j+1}`, summing to one over the allowed child pairs for each
`c ∈ A_j`, and child-exchange symmetric, `R((a, b) | c) = R((b, a) | c)`. -/
def IsNominalKernel (R : Kernel) : Prop :=
  ∀ j < 7, ∀ (r : Fin 13),
    (∀ c a b, 0 ≤ R j r c (a, b)) ∧
    (∀ c a b, R j r c (a, b) ≠ 0 → c ∈ alph j ∧ a ∈ alph (j + 1) ∧ b ∈ alph (j + 1) ∧ a + b = c) ∧
    (∀ c ∈ alph j, ∑ ab ∈ childPairs j, R j r c ab = 1) ∧
    (∀ c a b, R j r c (a, b) = R j r c (b, a))

/-- The nominal symbol distributions (39), p. 44 (also p. 12): `P_0^{(r)}(1) = ρ_r`,
`P_0^{(r)}(0) = 1 − ρ_r`, and `P_{j+1}^{(r)}(a) = Σ_b Γ_j^{(r)}(a, b)` with
`Γ_j^{(r)}(a, b) = P_j^{(r)}(a + b) R_j^{(r)}((a, b) | a + b)`. Distributions are zero outside their
alphabets. -/
noncomputable def nomP (R : Kernel) (ρ : Fin 13 → ℝ) (r : Fin 13) : ℕ → ℤ → ℝ
  | 0, c => if c = 1 then ρ r else if c = 0 then 1 - ρ r else 0
  | j + 1, a => ∑ b ∈ alph (j + 1), nomP R ρ r j (a + b) * R j r (a + b) (a, b)

open Classical in
/-- The stratum conditional entropy `H(R_j^{(r)} | P_j^{(r)}) = Σ_{c : P_j(c) > 0} P_j(c) H(R_j(· | c))`
(Definition 2.6, p. 10), in bits. -/
noncomputable def condEntropyStratum (R : Kernel) (ρ : Fin 13 → ℝ) (r : Fin 13) (j : ℕ) : ℝ :=
  ∑ c ∈ alph j, if 0 < nomP R ρ r j c then
    nomP R ρ r j c * entropyOn (childPairs j) (fun ab => R j r c ab) else 0

/-- The derived decomposition entropy rate `D_j = Σ_r w_r H(R_j^{(r)} | P_j^{(r)})` (§3.1, p. 12). -/
noncomputable def Drate (w : Fin 13 → ℝ) (R : Kernel) (ρ : Fin 13 → ℝ) (j : ℕ) : ℝ :=
  ∑ r, w r * condEntropyStratum R ρ r j

/-- The derived word entropy rate `H_j = Σ_r w_r H(P_j^{(r)})` (§3.1, p. 12). -/
noncomputable def Hrate (w : Fin 13 → ℝ) (R : Kernel) (ρ : Fin 13 → ℝ) (j : ℕ) : ℝ :=
  ∑ r, w r * entropyOn (alph j) (nomP R ρ r j)

/-- The tuples `A₂⁴` of the four depth-two symbols at one coordinate. -/
noncomputable def depthTwoTuples : Finset (ℤ × ℤ × ℤ × ℤ) :=
  alph 2 ×ˢ alph 2 ×ˢ alph 2 ×ˢ alph 2

/-- The joint distribution (40), p. 44, of the four depth-two symbols `u = (u₁, u₂, u₃, u₄)` at a
coordinate with root symbol `c` in stratum `r`:
`Γ^{(r,c)}_{2,[4]}(u) = R_0((u₁+u₂, u₃+u₄) | c) R_1((u₁, u₂) | u₁+u₂) R_1((u₃, u₄) | u₃+u₄)`. -/
noncomputable def gammaTwo (R : Kernel) (r : Fin 13) (c : ℤ) (u : ℤ × ℤ × ℤ × ℤ) : ℝ :=
  R 0 r c (u.1 + u.2.1, u.2.2.1 + u.2.2.2) * R 1 r (u.1 + u.2.1) (u.1, u.2.1) *
    R 1 r (u.2.2.1 + u.2.2.2) (u.2.2.1, u.2.2.2)

/-- Observation spaces: subspaces of `F₇³`, the row spaces of observation matrices `B` (§4.1,
p. 22). -/
abbrev ObsSpace := Submodule (ZMod 7) (Fin 3 → ZMod 7)

/-- The observation `g_B(u) = B (u₁, u₂, u₃)ᵀ mod 7` (§6.2, p. 44), written basis-free: the values
`⟨s, u[3]⟩ mod 7` of all row-space vectors `s ∈ S = row(B)`. It determines and is determined by
`B u[3] mod 7`, so its image distribution has the same entropy for every basis `B` of `S`. -/
def obsMap (S : ObsSpace) (u : ℤ × ℤ × ℤ × ℤ) : S → ZMod 7 :=
  fun s => s.1 0 * (u.1 : ZMod 7) + s.1 1 * (u.2.1 : ZMod 7) + s.1 2 * (u.2.2.1 : ZMod 7)

/-- The nominal depth-two observation entropy (9), p. 22, in its nominal form p. 44, for one
observation space `S = row(B)`:
`H(B V_{2,[3]} mod 7 | X, J) = Σ_r w_r Σ_{c ∈ {0,1}} P_0^{(r)}(c) H(g_B(Γ^{(r,c)}_{2,[4]}))`. -/
noncomputable def obsEntropy (w : Fin 13 → ℝ) (R : Kernel) (ρ : Fin 13 → ℝ) (S : ObsSpace) : ℝ :=
  ∑ r, w r * ∑ c ∈ ({0, 1} : Finset ℤ),
    nomP R ρ r 0 c * imageEntropy depthTwoTuples (gammaTwo R r c) (obsMap S)

/-- `e_sum = (1, 1, 0)`, the sum giving the first depth-one symbol (p. 22). -/
def esum : Fin 3 → ZMod 7 := ![1, 1, 0]

open Classical in
/-- `b₁(B) = dim(row(B) ∩ ⟨e_sum⟩)` (p. 22): `1` if `e_sum ∈ row(B)`, else `0`. -/
noncomputable def b1 (S : ObsSpace) : ℕ := if esum ∈ S then 1 else 0

/-- `b₂(B) = rank(B) − b₁(B)` (p. 22). -/
noncomputable def b2 (S : ObsSpace) : ℕ := Module.finrank (ZMod 7) S - b1 S

/-- Lexicographic order on depth-two tuples (Definition 2.2, p. 9: "tuples of symbols are ordered
lexicographically"). -/
def lexKey4 (u : ℤ × ℤ × ℤ × ℤ) : Lex (ℤ × Lex (ℤ × Lex (ℤ × ℤ))) :=
  toLex (u.1, toLex (u.2.1, toLex (u.2.2.1, u.2.2.2)))

/-- Lexicographic order on ordered pairs (Definition 2.2, p. 9). -/
def lexKey2 (ab : ℤ × ℤ) : Lex (ℤ × ℤ) := toLex ab

open Classical in
/-- `N^root_{r,c} = |{k ∈ I_r : x_k = c}|` (p. 23; Algorithm 2, p. 58). -/
noncomputable def rootSymCount (w : Fin 13 → ℝ) {n : ℕ} (x : Fin n → Fin 2) (r : Fin 13)
    (c : ℕ) : ℕ :=
  ((stratum w n r).filter (fun k => (x k).val = c)).card

/-- Exact depth-two joint counts (§6.2, p. 45; Algorithm 2 line 5, p. 58):
`N^root_{r,c} Γ̂^{(r,c)}_{2,[4]}` with `Γ̂^{(r,c)}_{2,[4]} = ⌊Γ^{(r,c)}_{2,[4]}⌉_{N^root_{r,c}}`, tuples
ordered lexicographically. -/
noncomputable def gammaTwoCount (w : Fin 13 → ℝ) (R : Kernel) {n : ℕ} (x : Fin n → Fin 2)
    (r : Fin 13) (c : ℕ) (u : ℤ × ℤ × ℤ × ℤ) : ℕ :=
  roundCount depthTwoTuples lexKey4 (gammaTwo R r (c : ℤ)) (rootSymCount w x r c) u

/-- The `v`-th coordinate (`v = 0, 1, 2, 3`) of a depth-two tuple. -/
def tupleCoord (u : ℤ × ℤ × ℤ × ℤ) : ℕ → ℤ
  | 0 => u.1
  | 1 => u.2.1
  | 2 => u.2.2.1
  | _ => u.2.2.2

/-- Exact child-pair counts at a parent slot of depth `j ≥ 2` (§6.2, p. 45; Algorithm 2 line 15):
for parent count `N = N^{(r)}_{j,v}(c) > 0`, the counts of `⌊R_j^{(r)}(· | c)⌉_N`, pairs ordered
lexicographically; `0` when `N = 0`. -/
noncomputable def condCount (R : Kernel) (r : Fin 13) (j : ℕ) (N : ℕ) (c : ℤ) (ab : ℤ × ℤ) : ℕ :=
  if N = 0 then 0 else roundCount (childPairs j) lexKey2 (R j r c) N ab

open Classical in
/-- Prescribed exact slot counts `n_r P̂^{(r)}_{j,v}(c)` for `2 ≤ j ≤ 7` (Algorithm 2, p. 58): at
depth two, the projections of the exact joint counts `Σ_c N^root_{r,c} Γ̂^{(r,c)}_{2,[4]}`
(line 6–10); at depth `j + 1 ≥ 3`, the marginals of the prescribed exact sibling counts
`N(c) R̂^{(r)}_{j,v}((a, b) | c)` of the parent slot (lines 16–17). Slot `v` at depth `j + 1` is the
left child (`v` even) or right child (`v` odd) of slot `⌊v/2⌋`. Depths `0, 1` are unused (`0`). -/
noncomputable def slotCount (w : Fin 13 → ℝ) (R : Kernel) {n : ℕ} (x : Fin n → Fin 2) (r : Fin 13) :
    ℕ → ℕ → ℤ → ℕ
  | 0, _, _ => 0
  | 1, _, _ => 0
  | 2, v, c => ∑ c0 ∈ ({0, 1} : Finset ℕ),
      ∑ u ∈ depthTwoTuples.filter (fun u => tupleCoord u v = c), gammaTwoCount w R x r c0 u
  | j + 3, v, a =>
      if v % 2 = 0 then
        ∑ b ∈ alph (j + 3),
          condCount R r (j + 2) (slotCount w R x r (j + 2) (v / 2) (a + b)) (a + b) (a, b)
      else
        ∑ b ∈ alph (j + 3),
          condCount R r (j + 2) (slotCount w R x r (j + 2) (v / 2) (b + a)) (b + a) (b, a)

open Classical in
/-- The **prescribed representation family** `𝒟` of the root `x` (§4.1, p. 19: "the nonempty set of
representations of x with the exact types constructed in Subsection 6.2"; §6.2, p. 45): the
representations of `x` such that
1. on each stratum `r` and for each root symbol `c`, the tuples of the four depth-two symbols have the
   exact joint counts `N^root_{r,c} Γ̂^{(r,c)}_{2,[4]}`;
2. at each slot `(j, v)` with `2 ≤ j ≤ 6`, on each stratum `r`, the sibling pairs `(a, b)` at the
   two children have the exact counts `N^{(r)}_{j,v}(a + b) R̂^{(r)}_{j,v}((a, b) | a + b)`.
The slot and sibling types at depths one and two are the images of the depth-two joint type. -/
noncomputable def exactFamily (w : Fin 13 → ℝ) (R : Kernel) (n : ℕ) (x : Fin n → Fin 2) :
    Finset (Rep n) :=
  (boundedReps n).filter (fun D =>
    IsRepOf x D ∧
    (∀ (r : Fin 13) (c : Fin 2) (u : ℤ × ℤ × ℤ × ℤ),
      ((stratum w n r).filter (fun k => x k = c ∧
        (D 2 ⟨0, by norm_num⟩ k, D 2 ⟨1, by norm_num⟩ k, D 2 ⟨2, by norm_num⟩ k,
          D 2 ⟨3, by norm_num⟩ k) = u)).card = gammaTwoCount w R x r c.val u) ∧
    (∀ (j : ℕ) (hj : 2 ≤ j ∧ j ≤ 6) (v : Fin (2 ^ j)) (r : Fin 13) (a b : ℤ),
      ((stratum w n r).filter (fun k =>
        D ⟨j + 1, by omega⟩ ⟨2 * v.val, by have := v.2; rw [pow_succ]; omega⟩ k = a ∧
        D ⟨j + 1, by omega⟩ ⟨2 * v.val + 1, by have := v.2; rw [pow_succ]; omega⟩ k = b)).card =
        condCount R r j (slotCount w R x r j v.val (a + b)) (a + b) (a, b)))

end RandModSubsetSum


