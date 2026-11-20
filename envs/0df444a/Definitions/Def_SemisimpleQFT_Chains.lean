-- Prove2me | Definitions.Def_SemisimpleQFT_Chains
-- name    : SemisimpleQFT_Chains
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-19T15:07:27.61018+00:00
-- url     : https://prove2.me/theorems/8131657c-3f2f-44e8-b8f2-b4ac72992e3e
-- title:
--   Bratteli diagrams, subalgebra adapted bases and the orthogonal form for the chains of $B_n(d)$, $B_{r,s}(d)$, $P_n(d)$
-- statement:
--   **Young diagrams.** `Shape N` is the set of Young diagrams with at most $N$ rows of length at most $N$, given by their weakly decreasing row lengths $\lambda_1\ge\dots\ge\lambda_N\ge0$; it contains every Young diagram with at most $N$ boxes. `size` is $|\lambda|=\sum_i\lambda_i$, and `AddBox μ ν` says $\nu=\mu+\square$ ($\mu_i\le\nu_i$ for all $i$ and $|\nu|=|\mu|+1$). `pairSize (λ, μ)` $=|\lambda|+|\mu|$.
--
--   **Bratteli diagrams and paths (pp. 34).** A `Bratteli V` has a set `vert t` of vertices at each level $t$ and edges `edge t μ ν` between a level-$t$ vertex $\mu$ and a level-$(t+1)$ vertex $\nu$. `Path t` is the set of paths $(\rho_0,\dots,\rho_t)$ with $\rho_i$ at level $i$ and consecutive entries joined; `last` is $\rho_t$, `trunc` drops the last entry (Eq. (5.22)), and `Vtx t` is the set of level-$t$ vertices.
--
--   **Subalgebra adapted systems (Sections 5.2–5.3).** For subalgebras $A_0,\dots,A_m$ (`alg t`) of an algebra and a Bratteli diagram $B$, a `GTSystem m alg B` consists of, for every $t\le m$, a Fourier isomorphism of $A_t$ (a `FourierData`) whose irreps are the level-$t$ vertices and whose basis indices are the Bratteli paths of length $t$, the irrep of a path being its endpoint; and it satisfies Eqs. (5.7)–(5.8): for $t<m$, $b\in A_t\cap A_{t+1}$ and paths $P,Q$ of length $t+1$ with the same endpoint $\rho$, $\rho(b)_{P,Q}=\sigma(b)_{P_{\le t},Q_{\le t}}$ if the truncations end at the same vertex $\sigma$, and $\rho(b)_{P,Q}=0$ otherwise. `top` is the Fourier isomorphism of $A_m$.
--
--   For a chain of diagram algebras, `IsStandard G size` says that the Fourier basis of the top algebra $A_m$ is in the orthogonal form ($\rho(D^{\mathrm{op}})=\rho(D)^\dagger$, Eq. (5.25)) and that its labelling satisfies Theorem 4.17 ($\rho(D)=0$ when $\mathrm{pn}(D)<|\rho|$).
--
--   **The three chains (Eqs. (5.23), (5.24)).** All algebras of a chain are spanned by diagrams with $n$ columns; an algebra on fewer columns is embedded by adding vertical strands (`HasStrand j D`: $\{j,j'\}$ is a block).
--   - `partitionLevel n t`, $0\le t\le 2n$: level $2k$ is $P_k(d)$ (strands in columns $k+1,\dots,n$), level $2k-1$ is $P_{k-1/2}(d)$ (in addition $k$ and $k'$ are in the same block). `partitionBratteli n`: the vertices at level $t$ are the $\lambda$ with $|\lambda|\le\lfloor t/2\rfloor$; from an even level to the next the shape stays or loses a box, from an odd level to the next it stays or gains a box (Eqs. (4.5), (4.6), (5.2), (5.3)).
--   - `brauerLevel n t`, $0\le t\le n$: $B_t(d)$, Brauer diagrams with strands in columns $t+1,\dots,n$. `brauerBratteli n`: vertices $\lambda$ with $|\lambda|\le t$, $|\lambda|\equiv t \pmod 2$; edges add or remove one box (Eqs. (4.7), (5.4)).
--   - `walledLevel r n t`, $0\le t\le n$ (for $r\le s=n-r$): $B_{a,b}(d)$ with $(a,b)=$ `walledSizes r t` $=(\lceil t/2\rceil,\lfloor t/2\rfloor)$ for $t\le 2r$ and $(r,t-r)$ afterwards — the chain $B_{0,0}\subseteq B_{1,0}\subseteq B_{1,1}\subseteq\dots\subseteq B_{r,r}\subseteq B_{r,r+1}\subseteq\dots\subseteq B_{r,s}$ — realised by the walled Brauer diagrams with strands in the left columns $a+1,\dots,r$ and the right columns $r+b+1,\dots,n$. `walledBratteli r n`: vertices $(\lambda,\mu)$ with $|\lambda|=a-k$, $|\mu|=b-k$; when a left column is added, $(\lambda',\mu')$ at the lower level is joined to $(\lambda,\mu)$ iff $\lambda'=\lambda-\square,\ \mu'=\mu$ or $\lambda'=\lambda,\ \mu'=\mu+\square$; when a right column is added, iff $\lambda'=\lambda+\square,\ \mu'=\mu$ or $\lambda'=\lambda,\ \mu'=\mu-\square$ (Eqs. (4.8), (5.5), (5.6)).
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, Sections 4.3 and 5, pp. 24–25 and 30–35: Theorems 4.12–4.15, Theorem 5.2, Eqs. (4.5)–(4.8), (5.2)–(5.8), (5.20)–(5.25)

import Definitions.Def_SemisimpleQFT_Diagram

/-!
# Bratteli diagrams, subalgebra adapted bases and the orthogonal form for diagram algebras

Source: B. Foxman, B. Nehoran, Y. Ding, *Efficient Quantum Fourier Transforms For Semisimple
Algebras*, Sections 4.3 and 5 (PDF pp. 24–25, 30–35).

Conventions:

* A Young diagram with at most `N` boxes is stored by its row lengths
  `λ_1 ≥ λ_2 ≥ … ≥ λ_N ≥ 0`, each at most `N` (`Shape N`).
* A chain `ℂ = A_0 ⊆ A_1 ⊆ … ⊆ A_m = A` (Eq. (5.20)) of diagram algebras is given by the
  diagram sets `level t` of its members, all inside the diagrams with `n` columns: a smaller
  algebra on fewer columns is embedded by adding vertical strands `{j, j'}` in the remaining
  columns.
* A Bratteli diagram (PDF p. 34) is given by its vertices at each level (the irrep labels of
  `A_t`) and its edges between consecutive levels (the branching rule of Theorem 5.2). The basis
  of the irrep space `V^ρ` of `A_t` is indexed by the Bratteli paths from the root to `ρ`
  (Eq. (5.21)).
-/

set_option warn.classDefReducibility false

namespace SemisimpleQFT

open scoped BigOperators ComplexConjugate

/-- PDF p. 24: a Young diagram with at most `N` rows, each of length at most `N`, given by its
weakly decreasing row lengths `λ_1 ≥ … ≥ λ_N` (`λ.1 i` is the length of row `i + 1`). Every
Young diagram with at most `N` boxes is of this form. -/
abbrev Shape (N : ℕ) := {f : Fin N → Fin (N + 1) // ∀ i j : Fin N, i ≤ j → f j ≤ f i}

/-- PDF p. 24: `|λ|`, the total number of boxes. -/
def Shape.size {N : ℕ} (s : Shape N) : ℕ := ∑ i : Fin N, (s.1 i : ℕ)

/-- Theorem 5.2 (PDF p. 31): `ν = μ + □`, i.e. `ν` is obtained from `μ` by adding one box. -/
def AddBox {N : ℕ} (μ ν : Shape N) : Prop :=
  (∀ i : Fin N, μ.1 i ≤ ν.1 i) ∧ ν.size = μ.size + 1

/-- PDF p. 34: a Bratteli diagram with vertex labels in `V`: `vert t` is the set of vertices at
level `t` (the irreps of `A_t`), and `edge t μ ν` says that the level-`t` vertex `μ` is joined
to the level-`(t+1)` vertex `ν` (i.e. `μ ∈ Res(ν)`). -/
structure Bratteli (V : Type) where
  /-- The vertices at each level. -/
  vert : ℕ → V → Prop
  /-- The edges from level `t` to level `t + 1`. -/
  edge : ℕ → V → V → Prop

namespace Bratteli

variable {V : Type}

/-- PDF p. 34, Eq. (5.21): a Bratteli path `(ρ_0, ρ_1, …, ρ_t)`: `ρ_i` is a vertex at level `i`
and consecutive entries are joined by an edge. -/
def Path (B : Bratteli V) (t : ℕ) : Type :=
  {p : Fin (t + 1) → V //
    (∀ i : Fin (t + 1), B.vert i.val (p i)) ∧
    (∀ i : Fin t, B.edge i.val (p i.castSucc) (p i.succ))}

instance (B : Bratteli V) (t : ℕ) [Finite V] : Finite (B.Path t) :=
  inferInstanceAs (Finite {q : Fin (t + 1) → V //
    (∀ i : Fin (t + 1), B.vert i.val (q i)) ∧
    (∀ i : Fin t, B.edge i.val (q i.castSucc) (q i.succ))})

noncomputable instance (B : Bratteli V) (t : ℕ) [Finite V] : Fintype (B.Path t) :=
  Fintype.ofFinite _

noncomputable instance (B : Bratteli V) (t : ℕ) : DecidableEq (B.Path t) := Classical.decEq _

/-- The entry `ρ_i = P(i)` of a path. -/
def Path.at {B : Bratteli V} {t : ℕ} (p : B.Path t) (i : Fin (t + 1)) : V := Subtype.val p i

/-- The endpoint `ρ_t` of a path, the irrep whose basis vector it indexes. -/
def Path.last {B : Bratteli V} {t : ℕ} (p : B.Path t) : V := Subtype.val p (Fin.last t)

/-- PDF p. 34, Eq. (5.22): the truncated path `P_{≤ t} = (ρ_0, …, ρ_t)` of a path of length
`t + 1`. -/
def Path.trunc {B : Bratteli V} {t : ℕ} (p : B.Path (t + 1)) : B.Path t :=
  ⟨fun i => Subtype.val p i.castSucc,
    fun i => (Subtype.property p).1 i.castSucc,
    fun i => (Subtype.property p).2 i.castSucc⟩

/-- The vertices at level `t`, as a type: the irrep labels of `A_t`. -/
def Vtx (B : Bratteli V) (t : ℕ) : Type := {v : V // B.vert t v}

end Bratteli

/-- Sections 5.2–5.3 (PDF pp. 32–34): a subalgebra adapted (Gelfand–Tsetlin) system of Fourier
bases for a chain `A_0 ⊆ A_1 ⊆ … ⊆ A_m` (`A_t = alg t`) of subalgebras of `R`, with respect to
a Bratteli diagram `B`.

* For each level `t ≤ m`, `F t` is a Fourier isomorphism of `A_t` whose irreps are labelled by
  the level-`t` vertices of `B` and whose basis of the irrep space `V^ρ` is indexed by the
  Bratteli paths ending at `ρ` (`lab_eq`).
* `adapted` is Eqs. (5.7)–(5.8) for the multiplicity-free branching given by the edges of `B`:
  for `b ∈ A_t` and paths `P, Q` to the same irrep `ρ` of `A_{t+1}`, the entry `ρ(b)_{P,Q}` is
  `σ(b)_{P_{≤t}, Q_{≤t}}` if the truncations of `P` and `Q` end at the same irrep `σ` of `A_t`,
  and `0` otherwise. -/
structure GTSystem {R : Type*} [Ring R] [Algebra ℂ R] (m : ℕ) (alg : ℕ → Subalgebra ℂ R)
    {V : Type} [Finite V] (B : Bratteli V) where
  /-- The Fourier isomorphism of `A_t`, with basis indexed by Bratteli paths. -/
  F : (t : ℕ) → t ≤ m → FourierData (alg t) (B.Vtx t) (B.Path t)
  /-- The irrep of a path is its endpoint. -/
  lab_eq : ∀ (t : ℕ) (ht : t ≤ m) (p : B.Path t), ((F t ht).lab p).1 = p.last
  /-- Eqs. (5.7)–(5.8): the basis of `A_{t+1}` is `A_t`-adapted. -/
  adapted : ∀ (t : ℕ) (ht : t + 1 ≤ m) (x : R) (hx : x ∈ alg t) (hx' : x ∈ alg (t + 1))
    (p q : B.Path (t + 1)), p.last = q.last →
    (p.trunc.last = q.trunc.last →
      (F (t + 1) ht).rep ⟨x, hx'⟩ p q =
        (F t (Nat.le_of_succ_le ht)).rep ⟨x, hx⟩ p.trunc q.trunc) ∧
    (p.trunc.last ≠ q.trunc.last → (F (t + 1) ht).rep ⟨x, hx'⟩ p q = 0)

namespace GTSystem

variable {n : ℕ} {m : ℕ} {level : ℕ → Set (Diagram n)} {d : ℕ} {V : Type} [Finite V]
  {B : Bratteli V}

/-- The Fourier isomorphism of the top algebra `A = A_m` of the chain. -/
def top {R : Type*} [Ring R] [Algebra ℂ R] {alg : ℕ → Subalgebra ℂ R}
    (G : GTSystem m alg B) : FourierData (alg m) (B.Vtx m) (B.Path m) :=
  G.F m le_rfl

/-- Sections 5.3–5.4 (PDF pp. 33–35): the subalgebra adapted system is in the orthogonal form
at the top algebra `A_m` (`ρ(D^{op}) = ρ(D)†`, Eq. (5.25)) and its labelling of the irreps of
`A_m` by Young diagrams satisfies Theorem 4.17 (`λ(D) = 0` whenever `pn(D) < |λ|`), `size`
being the number of boxes `|·|` of a label. -/
def IsStandard (G : GTSystem m (fun t => diagramAlgebra (level t) d) B) (size : V → ℕ) : Prop :=
  IsOrthogonalForm (S := level m) (d := d) G.top ∧
    IsVanishing (S := level m) (d := d) G.top (fun v => size v.1)

end GTSystem

variable {n : ℕ}

/-- The column `j` is a vertical strand of `D`: `{j, j'}` is a block of `D`. -/
def HasStrand (j : Fin n) (D : Diagram n) : Prop :=
  ∀ u : Vertex n, D (false, j) u ↔ (u = (false, j) ∨ u = (true, j))

/-- PDF p. 34, Eq. (5.23): the chain
`ℂ ≅ P_0(d) ⊆ P_{1/2}(d) ⊆ P_1(d) ⊆ … ⊆ P_{n-1/2}(d) ⊆ P_n(d)` inside the diagrams with `n`
columns. Level `t = 2k` is `P_k(d)`: the diagrams with vertical strands in the columns
`k+1, …, n`. Level `t = 2k - 1` is `P_{k-1/2}(d)`: those diagrams of `P_k(d)` in which `k` and
`k'` are in the same block. -/
def partitionLevel (n t : ℕ) : Set (Diagram n) :=
  {D | (∀ j : Fin n, (t + 1) / 2 ≤ j.val → HasStrand j D) ∧
    (t % 2 = 1 → ∀ j : Fin n, j.val + 1 = (t + 1) / 2 → D (false, j) (true, j))}

/-- Theorems 4.12, 4.13 and 5.2 (PDF pp. 25, 31, Eqs. (4.5), (4.6), (5.2), (5.3)): the Bratteli
diagram of the chain `partitionLevel`. The irreps of `P_k(d)` (level `2k`) are the `λ` with
`|λ| ≤ k`, those of `P_{k-1/2}(d)` (level `2k - 1`) the `λ` with `|λ| ≤ k - 1`. From an even
level to the next (`P_k ⊆ P_{k+1/2}`) the shape stays or loses a box; from an odd level to the
next (`P_{k-1/2} ⊆ P_k`) it stays or gains a box. -/
def partitionBratteli (n : ℕ) : Bratteli (Shape n) where
  vert t s := s.size ≤ t / 2
  edge t μ ν := if t % 2 = 0 then (ν = μ ∨ AddBox ν μ) else (ν = μ ∨ AddBox μ ν)

/-- PDF p. 34, Eq. (5.23): the chain `ℂ ≅ B_0(d) ⊆ B_1(d) ⊆ … ⊆ B_n(d)` inside the diagrams
with `n` columns: level `t` is `B_t(d)`, the Brauer diagrams with vertical strands in the
columns `t+1, …, n`. -/
def brauerLevel (n t : ℕ) : Set (Diagram n) :=
  {D | IsBrauer D ∧ ∀ j : Fin n, t ≤ j.val → HasStrand j D}

/-- Theorems 4.14 and 5.2 (PDF pp. 25, 31, Eqs. (4.7), (5.4)): the Bratteli diagram of the chain
`brauerLevel`: the irreps of `B_t(d)` are the `λ` with `|λ| ≤ t` and `|λ| ≡ t mod 2`, and at
each step the shape gains or loses one box. -/
def brauerBratteli (n : ℕ) : Bratteli (Shape n) where
  vert t s := s.size ≤ t ∧ s.size % 2 = t % 2
  edge _ μ ν := AddBox μ ν ∨ AddBox ν μ

/-- PDF p. 35, Eq. (5.24): the member `B_{a,b}(d)` at level `t` of the chain
`B_{0,0} ⊆ B_{1,0} ⊆ B_{1,1} ⊆ … ⊆ B_{r,r} ⊆ B_{r,r+1} ⊆ … ⊆ B_{r,s}` (for `r ≤ s`):
`(a, b) = (⌈t/2⌉, ⌊t/2⌋)` for `t ≤ 2r`, and `(a, b) = (r, t - r)` afterwards. -/
def walledSizes (r t : ℕ) : ℕ × ℕ :=
  if t ≤ 2 * r then ((t + 1) / 2, t / 2) else (r, t - r)

/-- PDF p. 35, Eq. (5.24): the chain of walled Brauer algebras inside the walled Brauer diagrams
with `n` columns and the wall after column `r`. Level `t` is `B_{a,b}(d)` with
`(a, b) = walledSizes r t`: the walled Brauer diagrams with vertical strands in the left columns
`a+1, …, r` and in the right columns `r+b+1, …, n`. -/
def walledLevel (r n t : ℕ) : Set (Diagram n) :=
  {D | IsWalled r D ∧ ∀ j : Fin n,
    (((walledSizes r t).1 ≤ j.val ∧ j.val < r) ∨ r + (walledSizes r t).2 ≤ j.val) →
      HasStrand j D}

/-- Theorems 4.15 and 5.2 (PDF pp. 25, 31, Eqs. (4.8), (5.5), (5.6)): the Bratteli diagram of the
chain `walledLevel`. The irreps of `B_{a,b}(d)` are the pairs `(λ, μ)` with `|λ| = a - k`,
`|μ| = b - k` for some `0 ≤ k ≤ min(a, b)`. When a left column is added
(`B_{a-1,b} ⊆ B_{a,b}`), the smaller pair `(λ', μ')` is joined to `(λ, μ)` if
`λ' = λ - □, μ' = μ` or `λ' = λ, μ' = μ + □`; when a right column is added
(`B_{a,b-1} ⊆ B_{a,b}`), if `λ' = λ + □, μ' = μ` or `λ' = λ, μ' = μ - □`. -/
def walledBratteli (r n : ℕ) : Bratteli (Shape n × Shape n) where
  vert t v := v.1.size ≤ (walledSizes r t).1 ∧ v.2.size ≤ (walledSizes r t).2 ∧
    (walledSizes r t).1 - v.1.size = (walledSizes r t).2 - v.2.size
  edge t v w :=
    if (walledSizes r (t + 1)).1 = (walledSizes r t).1 + 1 then
      (AddBox v.1 w.1 ∧ v.2 = w.2) ∨ (v.1 = w.1 ∧ AddBox w.2 v.2)
    else
      (AddBox w.1 v.1 ∧ v.2 = w.2) ∨ (v.1 = w.1 ∧ AddBox v.2 w.2)

/-- PDF p. 25: `|(λ, μ)| = |λ| + |μ|`. -/
def pairSize {N : ℕ} (v : Shape N × Shape N) : ℕ := v.1.size + v.2.size

end SemisimpleQFT


