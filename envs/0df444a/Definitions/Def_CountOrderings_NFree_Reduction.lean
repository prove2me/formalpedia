-- Prove2me | Definitions.Def_CountOrderings_NFree_Reduction
-- name    : CountOrderings_NFree_Reduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:57:11.412892+00:00
-- url     : https://prove2.me/theorems/197ecd46-6485-4564-a21c-d2c1b814fc37
-- title:
--   The DAG $A_{I,q}$, its edge poset $P_{I,q}$, and the quantities $\Omega_{le}$, $\rho_\sigma$, $C_{i,\sigma}$, $\chi_\sigma$, $E_X$, $\Omega_{xc}(X)$, $\#LE(P_{I,q})_\sigma$
-- statement:
--   Fix an instance $I$ of #X3C (definition `CountOrderings.NFree.X3C`) with sets $S_0, \dots, S_{n-1}$ and universe $U$, $|U| = 3h$, and an integer $q \ge 0$.
--
--   **The DAG $A_{I,q}$.** Vertices: a root $r$, a vertex $s_i$ for each set, a vertex $\tilde u_j$ for each $u_j \in U$, and copies $u_j^{(k)}$, $s_i^{(k)}$ for $k = 0, \dots, q-1$. Edges: $(s_i, \tilde u_j)$ whenever $u_j \in S_i$; $(r, s_i)$ for every $i$; $(\tilde u_j, u_j^{(k)})$; and $(s_i, s_i^{(k)})$. $P_{I,q}$ is the **edge poset** of $A_{I,q}$ (definition `CountOrderings.NFree.EdgePoset`). $E'$ is the set of edges $(s_i,\tilde u_j)$ and $(r, s_i)$; it does not depend on $q$, and $|E'| = 4n$. The DAG with vertices $r, s_i, \tilde u_j$ and edge set $E'$ is the **base DAG**.
--
--   **Orderings.** An ordering of $E'$ is a sequence $\sigma = (e^\sigma_1, \dots, e^\sigma_{4n})$ listing every edge of $E'$ once. $\Omega_{le}$ is the set of orderings of $E'$ that are linear extensions of the edge poset of the base DAG (every $(r, s_i)$ comes before every $(s_i, \tilde u_j)$). For $\sigma$ an ordering of $E'$:
--   $$\rho_\sigma(u_j) = \max\{i \mid e^\sigma_i = (s_\ell, \tilde u_j) \text{ for some } \ell\},$$
--   $$C_{i,\sigma} = \bigl|\{u_j \in U \mid \rho_\sigma(u_j) \ge 4n+1-i\}\bigr| + \bigl|\{\ell \mid (r, s_\ell) = e^\sigma_k \text{ for some } k \ge 4n+1-i\}\bigr| ,$$
--   $$\chi_\sigma(q) = \prod_{i=1}^{4n} \frac{1}{i + q\, C_{i,\sigma}} \qquad (q \in \mathbb{R}).$$
--   For a set $X$ of indices, $E_X = \{(r, s_i) \mid i \in X\} \cup \{(s_i, \tilde u_j) \mid i \in X,\ u_j \in S_i\}$, and $\Omega_{xc}(X)$ is the set of $\sigma \in \Omega_{le}$ whose last $4h$ edges $e^\sigma_{4n-4h+1}, \dots, e^\sigma_{4n}$ are exactly the edges of $E_X$, in some order ($\sigma$ **induces** $X$).
--
--   **The restricted count.** $\#\mathrm{LE}(P_{I,q})_\sigma$ is the number of linear extensions of $P_{I,q}$ whose projection down to $E'$ coincides with $\sigma$, i.e. in which the edges of $E'$ appear in the order $e^\sigma_1, \dots, e^\sigma_{4n}$.
--
--   **Formalization Note.** An ordering is a bijection $\sigma : \{0, \dots, 4n-1\} \to E'$; index $p$ is the paper's position $p+1$, and $C_{i,\sigma}$ keeps the paper's $1$-based $i$. $\rho_\sigma(u_j) = 0$ when no edge enters $\tilde u_j$ (excluded by the standing assumptions). The paper defines $\Omega_{le}$ as the orderings $\sigma$ with $\#\mathrm{LE}(P_{I,q})_\sigma > 0$ and shows on the same page that these are exactly the linear extensions of the edge poset of $E'$; the second description is used, so $\Omega_{le}$ visibly does not depend on $q$. $\chi_\sigma$ is a real function; at its poles Lean's convention $1/0 = 0$ applies, and statements about it take limits on punctured neighbourhoods only.
-- source:
--   Arenas, Schild and Subercaseaux, Hardness of Counting Orderings: Taking Gadget Amplification to the Limit, STOC 2027 submission, pp. 16–18 (PDF pp. 17–19), §6 (A_{I,q}, P_{I,q}, E', Ω_le, ρ_σ, C_{i,σ}, χ_σ, #LE(P_{I,q})_σ, E_X, Ω_xc(X))

import Mathlib
import Definitions.Def_FCP_LinearExtensions
import Definitions.Def_CountOrderings_NFree_EdgePoset
import Definitions.Def_CountOrderings_NFree_X3C

namespace CountOrderings.NFree

/-! ### The DAG `A_{I,q}` and its edge poset `P_{I,q}` (§6, p. 16) -/

/-- The vertices `r`, `s_i` (one per set) and `ũ_j` (one per universe element). -/
inductive BaseVertex (n m : ℕ)
  | root
  | set (i : Fin n)
  | elem (j : Fin m)

/-- The copies `u_j^{(k)}` and `s_i^{(k)}`, `k ∈ {0, …, q-1}`. -/
inductive CopyVertex (n m q : ℕ)
  | elemCopy (j : Fin m) (k : Fin q)
  | setCopy (i : Fin n) (k : Fin q)

/-- Candidate edges of steps (2) and (3): `(r, s_i)` and `(s_i, ũ_j)`. -/
inductive OrigEdgeRaw (n m : ℕ)
  | rootSet (i : Fin n)
  | setElem (i : Fin n) (j : Fin m)
  deriving DecidableEq, Fintype

/-- The edge `(s_i, ũ_j)` exists only when `u_j ∈ S_i`; every `(r, s_i)` exists. -/
def OrigEdgeRaw.Valid (I : X3CInstance) : OrigEdgeRaw I.n (3 * I.h) → Prop
  | .rootSet _ => True
  | .setElem i j => j ∈ I.S i

instance (I : X3CInstance) : DecidablePred (OrigEdgeRaw.Valid I) := fun e => by
  cases e <;> unfold OrigEdgeRaw.Valid <;> infer_instance

/-- `E'`: the edges introduced in steps (2) and (3) of the construction, `(r, s_i)` for every
`i` and `(s_i, ũ_j)` whenever `u_j ∈ S_i`. It does not depend on `q`. -/
def OrigEdge (I : X3CInstance) : Type := {e : OrigEdgeRaw I.n (3 * I.h) // e.Valid I}

instance (I : X3CInstance) : Fintype (OrigEdge I) :=
  inferInstanceAs (Fintype {e : OrigEdgeRaw I.n (3 * I.h) // e.Valid I})

instance (I : X3CInstance) : DecidableEq (OrigEdge I) :=
  inferInstanceAs (DecidableEq {e : OrigEdgeRaw I.n (3 * I.h) // e.Valid I})

/-- The edges of steps (4) and (5): `(ũ_j, u_j^{(k)})` and `(s_i, s_i^{(k)})`. -/
inductive CopyEdge (n m q : ℕ)
  | elemCopy (j : Fin m) (k : Fin q)
  | setCopy (i : Fin n) (k : Fin q)
  deriving DecidableEq, Fintype

/-- Tail of an edge of `E'`. -/
def OrigEdge.src {I : X3CInstance} (e : OrigEdge I) : BaseVertex I.n (3 * I.h) :=
  match e.1 with
  | .rootSet _ => .root
  | .setElem i _ => .set i

/-- Head of an edge of `E'`. -/
def OrigEdge.tgt {I : X3CInstance} (e : OrigEdge I) : BaseVertex I.n (3 * I.h) :=
  match e.1 with
  | .rootSet i => .set i
  | .setElem _ j => .elem j

/-- The index `i` of the set vertex `s_i` that an edge of `E'` is incident to. -/
def OrigEdge.setIdx {I : X3CInstance} (e : OrigEdge I) : Fin I.n :=
  match e.1 with
  | .rootSet i => i
  | .setElem i _ => i

/-- The DAG with vertices `r, s_i, ũ_j` and edge set `E'` (steps (1)–(3)). -/
def baseDAG (I : X3CInstance) : FinDAG where
  V := BaseVertex I.n (3 * I.h)
  E := OrigEdge I
  src := OrigEdge.src
  tgt := OrigEdge.tgt
  acyclic := by
    refine FinDigraph.isAcyclic_of_rank _
      (fun e : OrigEdge I => match e.1 with | .rootSet _ => 0 | .setElem _ _ => 1) ?_
    rintro ⟨e, he⟩ ⟨f, hf⟩ h
    cases e <;> cases f <;>
      simp_all [FinDigraph.Follows, OrigEdge.src, OrigEdge.tgt]

/-- **The DAG `A_{I,q}`** (p. 16): vertices `r`, `s_i`, `ũ_j`, `u_j^{(k)}`, `s_i^{(k)}`
(`1 ≤ k ≤ q`, here `k ∈ Fin q`); edges `(r, s_i)` for every `i`, `(s_i, ũ_j)` whenever
`u_j ∈ S_i`, `(ũ_j, u_j^{(k)})` and `(s_i, s_i^{(k)})`. Its edge type is `E_q = E' ⊕ E_q \ E'`. -/
def dagA (I : X3CInstance) (q : ℕ) : FinDAG where
  V := BaseVertex I.n (3 * I.h) ⊕ CopyVertex I.n (3 * I.h) q
  E := OrigEdge I ⊕ CopyEdge I.n (3 * I.h) q
  src
    | .inl e => .inl e.src
    | .inr (.elemCopy j _) => .inl (.elem j)
    | .inr (.setCopy i _) => .inl (.set i)
  tgt
    | .inl e => .inl e.tgt
    | .inr (.elemCopy j k) => .inr (.elemCopy j k)
    | .inr (.setCopy i k) => .inr (.setCopy i k)
  acyclic := by
    refine FinDigraph.isAcyclic_of_rank _
      (fun e : OrigEdge I ⊕ CopyEdge I.n (3 * I.h) q => match e with
        | .inl e => (match e.1 with | .rootSet _ => 0 | .setElem _ _ => 1)
        | .inr (.elemCopy _ _) => 2
        | .inr (.setCopy _ _) => 1) ?_
    rintro (⟨e, he⟩ | e) (⟨f, hf⟩ | f) h <;>
      (try cases e) <;> (try cases f) <;>
      simp_all [FinDigraph.Follows, OrigEdge.src, OrigEdge.tgt]

/-- **`P_{I,q}`**: the edge poset of `A_{I,q}`. -/
abbrev posetP (I : X3CInstance) (q : ℕ) : Type := EdgePoset (dagA I q)

/-! ### Orderings of `E'` and the quantities of §6 (pp. 16–18)

An ordering `σ = (e^σ_1, …, e^σ_{4n})` of `E'` is a bijection `σ : Fin (4n) ≃ E'`; the
`0`-based index `p` is the paper's position `p + 1`. -/

open Classical in
/-- **`Ω_le`**: the orderings `σ` of `E'` that are linear extensions of the edge poset of `E'`
(an edge `(r, s_i)` comes before every `(s_i, ũ_j)`). -/
noncomputable def omegaLE (I : X3CInstance) : Finset (Fin (4 * I.n) ≃ OrigEdge I) :=
  (Finset.univ : Finset (Fin (4 * I.n) ≃ OrigEdge I)).filter
    (fun σ => ∀ e f : OrigEdge I, (baseDAG I).EdgeLE e f → σ.symm e ≤ σ.symm f)

open Classical in
/-- **`ρ_σ(u_j)`** `= max{i | e^σ_i = (s_ℓ, ũ_j) for some ℓ}`: the (1-based) position in `σ` of
the last edge entering `ũ_j` (`0` if no edge enters `ũ_j`). -/
noncomputable def rho {I : X3CInstance} (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) :
    ℕ :=
  ((Finset.univ : Finset (Fin (4 * I.n))).filter
    (fun p => ∃ ℓ : Fin I.n, (σ p).1 = .setElem ℓ j)).sup (fun p => p.val + 1)

open Classical in
/-- **`C_{i,σ}`** `= |{u_j ∈ U | ρ_σ(u_j) ≥ 4n + 1 − i}| + |{ℓ ∈ [n] | (r, s_ℓ) = e^σ_k for some
k ≥ 4n + 1 − i}|` (positions are 1-based, `i ∈ {1, …, 4n}`). -/
noncomputable def Ccount {I : X3CInstance} (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (3 * I.h))).filter (fun j => 4 * I.n + 1 - i ≤ rho σ j)).card +
    ((Finset.univ : Finset (Fin I.n)).filter (fun ℓ => ∃ p : Fin (4 * I.n),
      4 * I.n + 1 - i ≤ p.val + 1 ∧ (σ p).1 = .rootSet ℓ)).card

/-- **`χ_σ(q)`** `= ∏_{i=1}^{4n} 1/(i + q · C_{i,σ})`, as a real function of `q`. -/
noncomputable def chi {I : X3CInstance} (σ : Fin (4 * I.n) ≃ OrigEdge I) (q : ℝ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 (4 * I.n), 1 / ((i : ℝ) + q * (Ccount σ i : ℝ))

open Classical in
/-- **`E_X`** `= {(r, s_i) | S_i ∈ X} ∪ {(s_i, ũ_j) | S_i ∈ X, u_j ∈ S_i}`. -/
noncomputable def edgesOf (I : X3CInstance) (X : Finset (Fin I.n)) : Finset (OrigEdge I) :=
  (Finset.univ : Finset (OrigEdge I)).filter (fun e => e.setIdx ∈ X)

open Classical in
/-- **`Ω_xc(X)`**: the orderings `σ ∈ Ω_le` that induce `X`, i.e. whose last `4h` edges are exactly
the edges of `E_X` (in some order). -/
noncomputable def omegaXC (I : X3CInstance) (X : Finset (Fin I.n)) :
    Finset (Fin (4 * I.n) ≃ OrigEdge I) :=
  (omegaLE I).filter (fun σ =>
    ((Finset.univ : Finset (Fin (4 * I.n))).filter
      (fun p => 4 * I.n - 4 * I.h ≤ p.val)).image σ = edgesOf I X)

/-- **`#LE(P_{I,q})_σ`**: the number of linear extensions of `P_{I,q}` whose projection down to
`E'` coincides with `σ` (the edges of `E'` appear in the order `σ`). -/
noncomputable def linExtCountGiven (I : X3CInstance) (q : ℕ)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) : ℕ :=
  {L | L ∈ FCP.Order.LinearExtensions (posetP I q) ∧
    ∀ a b : Fin (4 * I.n), a < b →
      L (Sum.inl (σ a) : OrigEdge I ⊕ CopyEdge I.n (3 * I.h) q) <
        L (Sum.inl (σ b) : OrigEdge I ⊕ CopyEdge I.n (3 * I.h) q)}.ncard

end CountOrderings.NFree


