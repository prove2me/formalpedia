-- Prove2me | Definitions.Def_TraceAdopt_LPReform_BiLP10
-- name    : TraceAdopt_LPReform_BiLP10
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:19.473178+00:00
-- url     : https://prove2.me/theorems/8e435915-0bea-4293-a436-972b1d57d404
-- title:
--   Formulation (10), pp. 39–40 — rooted binary tree decompositions, partitions, and the final binary program
-- statement:
--   **Rooted binary tree decomposition.** A tree decomposition $(T',\{X'_z\})$ of the undirected auxiliary graph $G'$ is *rooted binary* when it carries a root $z_{rt}$ and a parent map $\mathrm{par}$, with $\mathrm{par}(z_{rt})=z_{rt}$, every other node adjacent in $T'$ to its parent, every node reaching the root by iterating $\mathrm{par}$, and at most two children per node. For a vertex $p\in N'$, the subtree $T'_p$ consists of the nodes whose bag contains $p$; its root $z_0^p$ is a node of $T'_p$ that is the root of $T'$ or whose parent's bag does not contain $p$.
--
--   **Partitions.** For each firm $i$, sets $J^i_z$ ($z\in T'$) partition $J^i=\{j: i\in e_j\}$, with $J^i_z\subseteq X'_z\cap N_{SC}$ and $J^i_z\neq\emptyset$ only if $i\in X'_z$. For each supply chain $j$, sets $I^j_z$ partition $I^j=e_j$ in the same way.
--
--   **Bit ranges.** Let $c_{\max}=\max_ic_i$ and $\theta_{\max}=\max_j\theta_j-1$, and set $n_u=\lfloor\log_2c_{\max}\rfloor$ and $n_v=\lfloor\log_2\theta_{\max}\rfloor$, so that $\sum_{\tau=0}^{n_u}2^\tau$ bits represent every integer in $\{0,\ldots,c_{\max}\}$. Write $u_{iz}=\sum_{\tau=0}^{n_u}2^\tau u^\tau_{iz}$, and similarly $\tilde u_{iz}$, $v_{jz}$, $\tilde v_{jz}$ with $n_v$ for the latter two.
--
--   **Formulation (10).** The variables $s_i$, $\ell_{pq}$ (pairs in a common bag), and all bits are binary, and
--
--   1. $u_{iz}\le\sum_{j\in J^i_z}r_{ji}\ell_{ji}$ for $z\in T'_i$ (10a);
--   2. $\tilde u_{iz}\le u_{iz}+\sum_{z'}\tilde u_{iz'}$ for $z\in T'_i$ other than the root, the sum over the children $z'$ of $z$ inside $T'_i$ (10b);
--   3. $u_{iz_0^i}+\sum_{z'}\tilde u_{iz'}\ge c_i(1-s_i)$ at the root $z_0^i$ of $T'_i$, the sum over its children in $T'_i$ (10c);
--   4. $v_{jz}\le\sum_{i\in I^j_z}\ell_{ij}$, $\tilde v_{jz}\le v_{jz}+\sum_{z'}\tilde v_{jz'}$, and $v_{jz_0^j}+\sum_{z'}\tilde v_{jz'}\ge\theta_j-1$, likewise on $T'_j$ (10e)–(10g);
--   5. $\ell_{pq}+\ell_{qp}=1$ and $\ell_{pq}+\ell_{qx}+\ell_{xp}\le2$ for distinct $p,q,x$ in a common bag (10i)–(10j).
--
--   The partial sums split each long constraint of (5) along the tree decomposition, which is what keeps the treewidth of the intersection graph small.
--
--   **Formalization Note** Four corrections to the printed formulation are disclosed. (i) The bit ranges are those of the ILP (11) on p. 40, $u\in\{0,\ldots,c_{\max}\}$ and $v\in\{0,\ldots,\theta_{\max}\}$; the printed count (6), $\lfloor\log_2(c_{\max}+1)\rfloor-1$, is one bit short (with $c_1=2$ it caps $u$ at $1$). (ii) The root inequalities (10c), (10g) use $u_{iz_0^i}$, $v_{jz_0^j}$: the printed $\tilde u_{iz_0^i}$ is a variable that the domain lines on p. 40 do not declare. (iii) The children in (10b), (10c), (10f), (10g) are those inside $T'_i$, resp. $T'_j$, and $z_0$ is the node of the subtree nearest the root of $T'$, so that the recursion runs over the subtree as in the proof on p. 40. (iv) (10i), (10j) range over distinct vertices, as for (5). The partitions are taken as arbitrary data with the stated properties; the paper constructs one greedily on pp. 17–18, and its proofs use only these properties. Bits outside the subtrees, and $\tilde u$ at subtree roots, occur in no constraint. The useful/useless split of p. 18 is absorbed: on a node with $J^i_z=\emptyset$, (10a) reads $u_{iz}\le0$.
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, pp. 16–18, (6) and the partitions $J^i_z, I^j_z$; pp. 39–40, formulation (10) and ILP (11)

import Definitions.Def_TraceAdopt_LPReform_Model

namespace TraceAdopt.LPReform

/-- A rooted binary tree decomposition of the undirected auxiliary graph `G′`
(p. 16: "we assume wlog that T′ is binary"): a tree decomposition `(t, X')`, a
root `rt`, and the parent map `par` of `t` rooted at `rt` (every non-root node is
adjacent to its parent, and iterating `par` reaches the root), with at most two
children per node. -/
def IsRootedBinaryTD (I : Instance) {T : Type} [Fintype T] [DecidableEq T]
    (t : SimpleGraph T) (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T) :
    Prop :=
  RobertsonSeymour1986.GM5.IsTreeDecomposition (auxGraph I) t X' ∧
  par rt = rt ∧
  (∀ z, z ≠ rt → t.Adj z (par z)) ∧
  (∀ z, ∃ k : ℕ, par^[k] z = rt) ∧
  (∀ z, (Finset.univ.filter (fun z' => z' ≠ rt ∧ par z' = z)).card ≤ 2)

/-- The children of a node `z` of the rooted tree. -/
def children {T : Type} [Fintype T] [DecidableEq T] (rt : T) (par : T → T) (z : T) :
    Finset T :=
  Finset.univ.filter (fun z' => z' ≠ rt ∧ par z' = z)

/-- `z` is the root `z₀^v` of the subtree `T′_v` of bags containing the vertex `v`:
it contains `v`, and either it is the root of `T′` or its parent does not contain `v`
(the node of `T′_v` nearest the root of `T′`). -/
def IsSubtreeRoot (I : Instance) {T : Type} (X' : T → Finset (Fin I.n ⊕ Fin I.m))
    (rt : T) (par : T → T) (v : Fin I.n ⊕ Fin I.m) (z : T) : Prop :=
  v ∈ X' z ∧ (z = rt ∨ v ∉ X' (par z))

/-- The partitions of p. 17–18: for each firm `i`, the sets `J i z` (`z ∈ T′`)
partition `J^i = {j | i ∈ e_j}` and `J i z ⊆ X'_z ∩ N_SC` with `i ∈ X'_z`; for each
supply chain `j`, the sets `Ip j z` partition `I^j = e_j` with `Ip j z ⊆ X'_z ∩ N_F`
and `j ∈ X'_z`. -/
def IsPartitionData (I : Instance) {T : Type} (X' : T → Finset (Fin I.n ⊕ Fin I.m))
    (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n)) : Prop :=
  (∀ i z, ∀ j ∈ J i z, i ∈ I.e j ∧ Sum.inl i ∈ X' z ∧ Sum.inr j ∈ X' z) ∧
  (∀ i z z', z ≠ z' → Disjoint (J i z) (J i z')) ∧
  (∀ i j, i ∈ I.e j → ∃ z, j ∈ J i z) ∧
  (∀ j z, ∀ i ∈ Ip j z, i ∈ I.e j ∧ Sum.inl i ∈ X' z ∧ Sum.inr j ∈ X' z) ∧
  (∀ j z z', z ≠ z' → Disjoint (Ip j z) (Ip j z')) ∧
  (∀ j i, i ∈ I.e j → ∃ z, i ∈ Ip j z)

/-- Highest bit index for the firm partial sums `u, ũ`: values up to
`c_max = max_i c_i` need the bits `τ = 0, …, ⌊log₂ c_max⌋` (ILP (11), p. 40). -/
def nu (I : Instance) : ℕ := Nat.log 2 (Finset.univ.sup I.c)

/-- Highest bit index for the supply-chain partial sums `v, ṽ`: values up to
`θ_max = max_j θ_j - 1` (ILP (11), p. 40). -/
def nv (I : Instance) : ℕ := Nat.log 2 (Finset.univ.sup I.θ - 1)

/-- The integer value `∑_{τ=0}^{K} 2^τ b^τ` of a bit vector, as in (10d) and (10h). -/
def bitVal {K : ℕ} (b : Fin (K + 1) → ℕ) : ℕ := ∑ τ : Fin (K + 1), 2 ^ τ.val * b τ

/-- Binary feasibility for the paper's final formulation (10), pp. 39–40, on a
rooted binary tree decomposition `(X', rt, par)` of `G′` and partition data
`J, Ip`. The bit vectors `u i z, ũ i z` (resp. `v j z, ṽ j z`) encode the partial
sums by (10d) (resp. (10h)). Corrections disclosed in the item statement: the root
inequalities (10c), (10g) use `u` (resp. `v`) at the subtree root; the children in
(10b), (10c), (10f), (10g) are the children inside the subtree `T′_i` (resp. `T′_j`);
(10i), (10j) range over distinct vertices; the bit ranges are those of `nu`, `nv`. -/
def BiLP10Feasible (I : Instance) {T : Type} [Fintype T] [DecidableEq T]
    (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)
    (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n))
    (s : Fin I.n → ℕ) (ℓ : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ)
    (u ut : Fin I.n → T → Fin (nu I + 1) → ℕ)
    (v vt : Fin I.m → T → Fin (nv I + 1) → ℕ) : Prop :=
  -- binary domains
  (∀ i, s i ≤ 1) ∧
  (∀ z, ∀ p ∈ X' z, ∀ q ∈ X' z, ℓ p q ≤ 1) ∧
  (∀ i z τ, u i z τ ≤ 1 ∧ ut i z τ ≤ 1) ∧
  (∀ j z τ, v j z τ ≤ 1 ∧ vt j z τ ≤ 1) ∧
  -- (10a)
  (∀ i z, Sum.inl i ∈ X' z →
    bitVal (u i z) ≤ ∑ j ∈ J i z, I.r j i * ℓ (Sum.inr j) (Sum.inl i)) ∧
  -- (10b)
  (∀ i z, Sum.inl i ∈ X' z → ¬ IsSubtreeRoot I X' rt par (Sum.inl i) z →
    bitVal (ut i z) ≤ bitVal (u i z) +
      ∑ z' ∈ (children rt par z).filter (fun z' => Sum.inl i ∈ X' z'), bitVal (ut i z')) ∧
  -- (10c), with `u` at the root
  (∀ i z, IsSubtreeRoot I X' rt par (Sum.inl i) z →
    I.c i ≤ bitVal (u i z) +
      (∑ z' ∈ (children rt par z).filter (fun z' => Sum.inl i ∈ X' z'), bitVal (ut i z')) +
      I.c i * s i) ∧
  -- (10e)
  (∀ j z, Sum.inr j ∈ X' z →
    bitVal (v j z) ≤ ∑ i ∈ Ip j z, ℓ (Sum.inl i) (Sum.inr j)) ∧
  -- (10f)
  (∀ j z, Sum.inr j ∈ X' z → ¬ IsSubtreeRoot I X' rt par (Sum.inr j) z →
    bitVal (vt j z) ≤ bitVal (v j z) +
      ∑ z' ∈ (children rt par z).filter (fun z' => Sum.inr j ∈ X' z'), bitVal (vt j z')) ∧
  -- (10g), with `v` at the root
  (∀ j z, IsSubtreeRoot I X' rt par (Sum.inr j) z →
    I.θ j - 1 ≤ bitVal (v j z) +
      ∑ z' ∈ (children rt par z).filter (fun z' => Sum.inr j ∈ X' z'), bitVal (vt j z')) ∧
  -- (10i)
  (∀ z, ∀ p ∈ X' z, ∀ q ∈ X' z, p ≠ q → ℓ p q + ℓ q p = 1) ∧
  -- (10j)
  (∀ z, ∀ p ∈ X' z, ∀ q ∈ X' z, ∀ x ∈ X' z, p ≠ q → q ≠ x → p ≠ x →
    ℓ p q + ℓ q x + ℓ x p ≤ 2)

end TraceAdopt.LPReform


