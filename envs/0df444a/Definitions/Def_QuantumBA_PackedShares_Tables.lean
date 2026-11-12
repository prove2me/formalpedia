-- Prove2me | Definitions.Def_QuantumBA_PackedShares_Tables
-- name    : QuantumBA_PackedShares_Tables
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:48.504169+00:00
-- url     : https://prove2.me/theorems/80349576-e5be-4882-8e9d-f2f50c8d09f1
-- title:
--   Committee properties (Lemma 4.4), forwarding-graph properties (Lemma 5.3), and first valid public tables
-- statement:
--   Write $L=\lceil\log_2 n\rceil$ and, for $\varepsilon,\beta>0$, $K(m)=\frac{2}{\varepsilon^2}\Bigl(\frac{n\ln 2+2}{\max\{1,\beta m\}}+\ln\frac e\beta\Bigr)$.
--
--   An assignment of committees $C_1,\dots,C_m\subseteq P=[n]$ of size $k$ to the $m$ nodes of a level has the **properties of Lemma 4.4** if (1) for every $F\subseteq P$ with $|F|\le t$ at most $\beta m$ committees satisfy $|C\cap F|>\gamma|C|$, where $\gamma=1/3-\varepsilon/2$, and (2) every process lies in at most $\Delta=\lceil\max\{2emk/n,3L\}\rceil$ committees.
--
--   A bipartite graph from rows $U$ ($|U|=k$) to columns $V$ ($|V|=k'$) has the **properties of Lemma 5.3** for sampler error $\rho$ and out-degree $D$ if (i) every row has $D$ distinct neighbours, (ii) every column has degree at most $J_{\mathrm{graph}}=\lceil\max\{2ekD/k',3L\}\rceil$ ($J_{\mathrm{graph}}=k$ if $D=k'$), and (iii) for every $Z\subseteq V$,
--   $$\#\Bigl\{u\in U:\ \frac{|N(u)\cap Z|}{D}>\frac{|Z|}{k'}+\rho\Bigr\}\le\rho k .$$
--
--   The public tables used by the algorithm are the **first valid tables** in a fixed public order (exhaustive search): the valid indicator table of least code under a fixed injective encoding into $\mathbb N$, and a fixed default if none exists. A level with $k=n$ assigns $P$ to every node.
--
--   **Formalization Note** Graphs are stated on committee positions $\{0,\dots,k-1\}$ and $\{0,\dots,k'-1\}$.
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, p. 20, Lemma 4.4 and §C.2 (PDF pp. 21, 38–39); p. 29, Lemma 5.3 and §C.3 (PDF pp. 30, 39)

import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace QuantumBA.PackedShares

/-! # Public committees (Lemma 4.4) and forwarding graphs (Lemma 5.3), and the "first valid
table in a fixed public order" rule -/

/-- `L = ⌈log₂ n⌉`. -/
def logL (n : ℕ) : ℕ := Nat.clog 2 n

/-- `K(m) = (2/ε²)((n ln 2 + 2)/max{1, βm} + ln(e/β))` of Lemma 4.4. -/
noncomputable def Kbound (ε β : ℝ) (n m : ℕ) : ℝ :=
  2 / ε ^ 2 * ((n * Real.log 2 + 2) / max 1 (β * m) + Real.log (Real.exp 1 / β))

/-- The two properties of Lemma 4.4 for an assignment `C` of committees of size `k` to the `m`
nodes of a level, with corruption fraction `γ = 1/3 - ε/2`: (1) for every `F ⊆ P` with
`|F| ≤ t`, at most `βm` committees have `|C ∩ F| > γ|C|`; (2) every process lies in at most
`Δ = ⌈max{2emk/n, 3L}⌉` committees. -/
def CommitteeProps (ε β : ℝ) (n t m k : ℕ) (C : Fin m → Finset (Fin n)) : Prop :=
  (∀ v, (C v).card = k) ∧
  (∀ Fs : Finset (Fin n), Fs.card ≤ t →
    ((Finset.univ.filter (fun v => (1 / 3 - ε / 2) * ((C v).card : ℝ) < ((C v ∩ Fs).card : ℝ))).card : ℝ)
      ≤ β * m) ∧
  (∀ p : Fin n, ((Finset.univ.filter (fun v => p ∈ C v)).card : ℝ) ≤
    (⌈max (2 * Real.exp 1 * m * k / n) (3 * (logL n : ℝ))⌉ : ℤ))

/-- `J_graph = ⌈max{2ekD/k', 3L}⌉`, or `k` if `D = k'` (Lemma 5.3 (ii)). -/
noncomputable def Jgraph (n k k' D : ℕ) : ℤ :=
  if D = k' then k else ⌈max (2 * Real.exp 1 * k * D / k') (3 * (logL n : ℝ))⌉

/-- Properties (i)–(iii) of Lemma 5.3 for a bipartite graph `N` from rows `Fin k` to columns
`Fin k'` with sampler error `ρ`: (i) every row has `D` distinct neighbours; (ii) every column has
degree at most `J_graph`; (iii) for every `Z ⊆ V`, at most `ρk` rows `u` have
`|N(u) ∩ Z|/D > |Z|/k' + ρ`. -/
def GraphProps (ρ : ℝ) (n k k' D : ℕ) (N : Fin k → Finset (Fin k')) : Prop :=
  (∀ u, (N u).card = D) ∧
  (∀ v : Fin k', (((Finset.univ.filter (fun u => v ∈ N u)).card : ℕ) : ℤ) ≤ Jgraph n k k' D) ∧
  (∀ Z : Finset (Fin k'),
    ((Finset.univ.filter (fun u => ((N u ∩ Z).card : ℝ) / D > (Z.card : ℝ) / k' + ρ)).card : ℝ) ≤ ρ * k)

/-- The first element, in the fixed public order given by the encoding `Encodable.encode`, that
satisfies `P`; the default `d` if there is none.  (Exhaustive search, §1.1 and §C.2.) -/
noncomputable def firstValid {α : Type} [Encodable α] (P : α → Prop) (d : α) : α := by
  classical
  exact if h : ∃ k : ℕ, ∃ a : α, Encodable.encode a = k ∧ P a
    then (Nat.find_spec h).choose else d

/-- Finsets of `Fin m` as indicator vectors (for the public enumeration). -/
def ofIndicator {m : ℕ} (f : Fin m → Bool) : Finset (Fin m) := Finset.univ.filter (fun i => f i = true)

/-- The public committee table of a level with `m` nodes and committee size `k`: all committees
are `P` if `k = n`; otherwise the first assignment (in the public order) with the properties of
Lemma 4.4; if none existed, the default assigns `P` to every node. -/
noncomputable def committeeTable (ε β : ℝ) (n t m k : ℕ) : Fin m → Finset (Fin n) :=
  if k = n then fun _ => Finset.univ else
    let T := firstValid (fun f : Fin m → Fin n → Bool =>
      CommitteeProps ε β n t m k (fun v => ofIndicator (f v))) (fun _ _ => true)
    fun v => ofIndicator (T v)

/-- The public forwarding graph from a committee of size `k` (rows, positions in increasing
identifier order) to its parent committee of size `k'` (columns): the first graph (in the public
order) with properties (i)–(iii) of Lemma 5.3; if none existed, the default joins every row to
all columns. -/
noncomputable def forwardingGraph (ρ : ℝ) (n k k' D : ℕ) : Fin k → Finset (Fin k') :=
  let T := firstValid (fun f : Fin k → Fin k' → Bool => GraphProps ρ n k k' D (fun u => ofIndicator (f u)))
    (fun _ _ => true)
  fun u => ofIndicator (T u)

end QuantumBA.PackedShares


