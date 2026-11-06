-- Prove2me | Definitions.Def_StrongConvG4
-- name    : StrongConvG4
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-05T22:12:03.583397+00:00
-- url     : https://prove2.me/theorems/5b8eaba3-c4c5-43d9-b0cd-01309ff8fb21
-- title:
--   Stable representations, the representations λ[N], and Hanany–Puder's quotient graphs (Chen–Garza-Vargas–Tropp–van Handel 2026, §10)
-- statement:
--   Objects for §10 of Chen–Garza-Vargas–Tropp–van Handel's paper and for the results of Hanany–Puder that it cites. Page numbers are those of arXiv:2405.16026v3 for the paper, and of arXiv:2009.00897v4 for L. Hanany and D. Puder, *Word measures on symmetric groups*, Int. Math. Res. Not. IMRN 2023 (11), 9221–9297, https://doi.org/10.1093/imrn/rnac084 (v5 has the same numbering and pages). Stable representations, $\xi_i$, `StableRep.model` and `NoTrivialSummand` come from the mission's bundle `Def_StrongConv`.
--
--   **The exponent $\beta$ (p. 30).** “Throughout this section, we fix a stable representation as in section 3.4.2 and adopt the notations introduced there. In addition, we will denote by $\beta$ the degree of the polynomial $\varphi(x_1, x_2^2, \dots, x_r^r)$”. `StableRep.beta π` is the total degree of the polynomial obtained from the character polynomial $\varphi$ by substituting $x_i^i$ for $x_i$.
--
--   **The representations $\lambda[N]$ (p. 14).** “Fix a base partition $\lambda = (\lambda_1 \ge \cdots \ge \lambda_\ell > 0) \vdash |\lambda|$ of $|\lambda| = \sum_{i=1}^\ell \lambda_i$. Then for every $N \ge |\lambda| + \lambda_1$, the irreducible representation of $\mathbf S_N$ defined by $$\lambda[N] = (N - |\lambda| \ge \lambda_1 \ge \cdots \ge \lambda_\ell) \vdash N \qquad (3.2)$$ is stable.”
--   - A base partition is a Mathlib `YoungDiagram` $\mu$; $|\lambda|$ is its number of cells, $\lambda_1$ is `μ.rowLen 0`, and its row lengths are `μ.rowLens`. `stableRows μ N` is the list of row lengths $(N - |\lambda|, \lambda_1, \dots, \lambda_\ell)$ of $\lambda[N]$. It is a partition of $N$ when $N \ge |\lambda| + \lambda_1$, the paper's range, and the statements use it only there.
--   - The paper does not construct the representation of $\mathbf S_N$ defined by a partition; the bundle uses the Young symmetrizer construction of W. Fulton and J. Harris, *Representation Theory: A First Course*, Graduate Texts in Mathematics 129, Springer, 1991, https://doi.org/10.1007/978-1-4612-0979-9, Lecture 4 (§4.1). For row lengths $\mu_1, \mu_2, \dots$ summing to $N$, fill the rows in order with $0, 1, \dots, N-1$; `tabRow` and `tabCol` give the row and column of an entry. With $P$ the permutations preserving every row and $Q$ those preserving every column, $a = \sum_{p \in P} p$ and $b = \sum_{q \in Q} \operatorname{sgn}(q)\, q$ in the group algebra $\mathbb C[\mathbf S_N]$, and `youngSymmetrizer N rows` is $c = ab$. `youngSpace N rows` is the left ideal $\mathbb C[\mathbf S_N]\, c$ as a complex vector space, and `youngAct N rows σ` is left multiplication by $\sigma$ on it. Fulton–Harris's Theorem 4.3 identifies this with the irreducible representation indexed by the partition. In Lean, `StrongConv.exists_linearEquiv_youngSpace_specht` states that for a Young diagram $\mu$ with $N$ cells, `youngSpace N μ.rowLens` with the action `youngAct` is isomorphic to the Specht module of shape $\mu$ (`OAI.Saxl.Specht`); Specht modules are irreducible (`OAI.Saxl.specht_irreducible`), and every irreducible representation of $\mathbf S_N$ is one (`OAI.Saxl.irreducible_equiv_specht`).
--
--   **Hanany–Puder's multi core graph $\Gamma^w_{\alpha_1, \dots, \alpha_r}$ (HP p. 16).** HP, Example 3.6: “Here there is a multiset $\mathcal H \in \mathcal{MOCC}(\mathbf F)$ of size $\alpha_1 + \ldots + \alpha_k$, with $\alpha_1$ copies of $\langle w\rangle^{\mathbf F}$, $\alpha_2$ copies of $\langle w^2\rangle^{\mathbf F}$, and so on. The corresponding multi core graph is denoted $\Gamma^w_{\alpha_1,\dots,\alpha_k} \overset{\rm def}{=} \Gamma_B(\mathcal H)$. It consists of $\alpha_1$ disjoint copies of a cycle of length $|w|_c$ depicting $w$, together with $\alpha_2$ disjoint copies of a cycle of length $|w^2|_c$ depicting $w^2$, and so on, where $|w|_c$ denotes the length of the cyclic reduction of $w$.”
--   - A word of $\mathbf F_d$ is written as a list of letters $(i, \mathrm{true})$ for $x_i$ and $(i, \mathrm{false})$ for $x_i^{-1}$, and $L$ is its cyclic reduction (in the statements, `FreeGroup.reduceCyclically w.toWord`). `cycleWord L j` is $L$ repeated $j$ times, the labels around the cycle depicting $w^j$.
--   - `CycleVert L α` is the vertex set: for each $i$, $\alpha_i$ copies of a cycle of length $i\,|w|_c$ (the copy is indexed by $i - 1$ and a number below $\alpha_i$), and a position on the cycle. Each position $p$ carries one edge, between $p$ and $p + 1$ (cyclically), labeled by the letter `edgeLetter` in place $p$: for $x_i$ it runs from $p$ to $p + 1$ (`edgeTail`, `edgeHead`), for $x_i^{-1}$ from $p + 1$ to $p$.
--
--   **Quotients (HP p. 26).** HP, after Definition 6.4: “$\mathcal D\mathrm{ecomp}_B(\eta)$ can be thought of as the set of all partitions of $V(\Gamma)$, the vertex-set of $\Gamma$, which give rise (without folding) to valid multi core graphs, and which are finer than (or equal to) the partition induced by $\eta$.” A partition $P$ of the vertices is a `Finpartition`. Its quotient graph has the blocks as vertices and an edge labeled $j$ from block $B_1$ to block $B_2$ whenever an edge labeled $j$ of $\Gamma$ runs from a vertex of $B_1$ to a vertex of $B_2$ (HP p. 23).
--   - `IsFoldFree P`: the quotient needs no folding, that is, two edges with the same label have tails in the same block exactly when they have heads in the same block. Then each block has at most one outgoing and at most one incoming edge of each label.
--   - CGTvH p. 30: “Here we denote by $v_\Gamma$ the number of vertices of $\Gamma$, by $e^j_\Gamma$ the number of edges of $\Gamma$ colored by $j$, and by $e_\Gamma = e^1_\Gamma + \cdots + e^d_\Gamma$.” `quotVert P` is $v_\Gamma$, the number of blocks, and `quotEdge P j` is $e^j_\Gamma$, the number of edges labeled $j$ of the quotient graph; $e_\Gamma$ is their sum over $j$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 30, β (p. 30), the representations λ[N] of §3.4 and the quotient graphs of Hanany–Puder used in Lemma 10.1, with Hanany, L. and Puder, D., Word measures on symmetric groups, Int. Math. Res. Not. IMRN 2023 (2023) 9221–9297, https://doi.org/10.1093/imrn/rnac084 (arXiv:2009.00897v4)

import Mathlib
import Definitions.Def_StrongConv

/-!
# Stable representations: `β`, the representations `λ[N]`, and Hanany–Puder's quotient graphs

C.-F. Chen, J. Garza-Vargas, J. A. Tropp and R. van Handel, *A new approach to strong convergence*,
Ann. of Math. 203 (2026) 555–602, arXiv:2405.16026v3 (CGTvH), §3.4.1 (p. 14) and §10 (pp. 30–31);
L. Hanany and D. Puder, *Word measures on symmetric groups*, Int. Math. Res. Not. IMRN 2023,
9221–9297, arXiv:2009.00897v4 (HP), Example 3.6 (p. 16) and §6.1 (p. 26).

Conventions:
- A partition is given by its list of row lengths. The representation of `S_N` defined by a
  partition is the left ideal of the group algebra `ℂ[S_N]` generated by the Young symmetrizer of
  the tableau that fills the rows in order with `0, 1, …, N - 1` (Fulton–Harris, *Representation
  Theory*, Lecture 4), with `σ` acting by left multiplication.
- A base partition `λ` is a Young diagram; `|λ|` is its number of cells and `λ₁` its first row
  length.
- A reduced word in `F_d` is a list of letters `(i, true)` for `x_i` and `(i, false)` for `x_i⁻¹`.
-/

noncomputable section

namespace StrongConv

namespace StableRep

/-- CGTvH p. 30: `β`, the degree of the polynomial `φ(x₁, x₂², …, x_r^r)`. -/
def beta (π : StableRep) : ℕ :=
  (MvPolynomial.aeval (fun i : Fin π.r =>
    (MvPolynomial.X i : MvPolynomial (Fin π.r) ℂ) ^ ((i : ℕ) + 1)) π.φ).totalDegree

end StableRep

/-! ## The representation of `S_N` defined by a partition -/

/-- The row of the entry `x` in the tableau with row lengths `rows` filled in order with
`0, 1, 2, …`: the number of rows `i` with `rows₀ + ⋯ + rows_i ≤ x`. -/
def tabRow (rows : List ℕ) (x : ℕ) : ℕ :=
  ((List.range rows.length).filter fun i => (rows.take (i + 1)).sum ≤ x).length

/-- The column of the entry `x` in the same tableau. -/
def tabCol (rows : List ℕ) (x : ℕ) : ℕ :=
  x - (rows.take (tabRow rows x)).sum

/-- The Young symmetrizer `c = a b ∈ ℂ[S_N]` of that tableau: `a` is the sum of the permutations
preserving every row and `b` the signed sum of the permutations preserving every column. -/
def youngSymmetrizer (N : ℕ) (rows : List ℕ) : MonoidAlgebra ℂ (Equiv.Perm (Fin N)) :=
  (∑ p ∈ Finset.univ.filter (fun p : Equiv.Perm (Fin N) =>
      ∀ x : Fin N, tabRow rows (p x : ℕ) = tabRow rows (x : ℕ)),
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) p) *
  (∑ q ∈ Finset.univ.filter (fun q : Equiv.Perm (Fin N) =>
      ∀ x : Fin N, tabCol rows (q x : ℕ) = tabCol rows (x : ℕ)),
    ((Equiv.Perm.sign q : ℤ) : ℂ) • MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) q)

/-- The space of the representation of `S_N` defined by the partition with row lengths `rows`: the
left ideal `ℂ[S_N] c` generated by the Young symmetrizer, as a complex vector space. -/
def youngSpace (N : ℕ) (rows : List ℕ) : Submodule ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin N))) :=
  (Submodule.span (MonoidAlgebra ℂ (Equiv.Perm (Fin N))) {youngSymmetrizer N rows}).restrictScalars ℂ

/-- The action of `σ ∈ S_N` on `youngSpace N rows`, by left multiplication. -/
def youngAct (N : ℕ) (rows : List ℕ) (σ : Equiv.Perm (Fin N)) :
    youngSpace N rows →ₗ[ℂ] youngSpace N rows :=
  (LinearMap.mulLeft ℂ (MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) σ)).restrict (fun x hx => by
    rw [youngSpace, Submodule.restrictScalars_mem] at hx ⊢
    exact (Submodule.span (MonoidAlgebra ℂ (Equiv.Perm (Fin N))) {youngSymmetrizer N rows}).smul_mem
      (MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) σ) hx)

/-- CGTvH (3.2), p. 14: the row lengths `(N - |λ|, λ₁, …, λ_ℓ)` of `λ[N]`, for a base partition
`λ`. -/
def stableRows (μ : YoungDiagram) (N : ℕ) : List ℕ :=
  (N - μ.cells.card) :: μ.rowLens

end StrongConv

/-! ## Hanany–Puder: the multi core graph `Γ^w_{α₁,…,α_r}` and its quotients -/

namespace HananyPuder

variable {d r : ℕ}

/-- The labels around the cycle depicting `w^j`: the letters `L` of `w` repeated `j` times. -/
def cycleWord (L : List (Fin d × Bool)) (j : ℕ) : List (Fin d × Bool) :=
  (List.replicate j L).flatten

/-- HP Example 3.6, p. 16: the vertices of `Γ^w_{α₁,…,α_r}`, which consists of `α_i` disjoint
cycles depicting `w^i` for each `i`, where `L` is the cyclic reduction of `w`. A vertex is a copy
`⟨i - 1, c⟩` together with a position on its cycle. -/
abbrev CycleVert (L : List (Fin d × Bool)) (α : Fin r → ℕ) : Type :=
  Σ c : (Σ i : Fin r, Fin (α i)), Fin (cycleWord L ((c.1 : ℕ) + 1)).length

variable {L : List (Fin d × Bool)} {α : Fin r → ℕ}

/-- The letter on the edge between position `p` and position `p + 1` of a cycle. The edges of
`Γ^w_{α₁,…,α_r}` are indexed by their first position `p`. -/
def edgeLetter (v : CycleVert L α) : Fin d × Bool :=
  (cycleWord L ((v.1.1 : ℕ) + 1))[v.2]

/-- The next position on the same cycle. -/
def nextVert (v : CycleVert L α) : CycleVert L α :=
  ⟨v.1, ⟨((v.2 : ℕ) + 1) % (cycleWord L ((v.1.1 : ℕ) + 1)).length,
    Nat.mod_lt _ (Nat.zero_lt_of_lt v.2.2)⟩⟩

/-- The tail of the edge at position `p`: the edge of a letter `x_i` runs from `p` to `p + 1`,
and the edge of a letter `x_i⁻¹` from `p + 1` to `p`. -/
def edgeTail (e : CycleVert L α) : CycleVert L α :=
  if (edgeLetter e).2 then e else nextVert e

/-- The head of the edge at position `p`. -/
def edgeHead (e : CycleVert L α) : CycleVert L α :=
  if (edgeLetter e).2 then nextVert e else e

/-- HP §6.1, p. 26: the partition `P` of the vertices generates a multi core graph without
folding: two edges with the same label have tails in the same block if and only if they have heads
in the same block. -/
def IsFoldFree (P : Finpartition (Finset.univ : Finset (CycleVert L α))) : Prop :=
  ∀ e e' : CycleVert L α, (edgeLetter e).1 = (edgeLetter e').1 →
    (P.part (edgeTail e) = P.part (edgeTail e') ↔ P.part (edgeHead e) = P.part (edgeHead e'))

instance (P : Finpartition (Finset.univ : Finset (CycleVert L α))) : Decidable (IsFoldFree P) := by
  unfold IsFoldFree; infer_instance

/-- `v_Γ`: the number of vertices (blocks) of the quotient graph of `P`. -/
def quotVert (P : Finpartition (Finset.univ : Finset (CycleVert L α))) : ℕ :=
  P.parts.card

/-- `e_Γ^j`: the number of edges labeled `j` of the quotient graph of `P`, edges with the same
label, tail block and head block being identified. -/
def quotEdge (P : Finpartition (Finset.univ : Finset (CycleVert L α))) (j : Fin d) : ℕ :=
  ((Finset.univ.filter fun e : CycleVert L α => (edgeLetter e).1 = j).image
    fun e => (P.part (edgeTail e), P.part (edgeHead e))).card

end HananyPuder

end


