-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
-- name    : OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T02:59:56.481391+00:00
-- url     : https://prove2.me/theorems/48d593e5-02d5-4236-a058-4dc5a074cdcf
-- title:
--   Finite selector and terminal tables on a routing tree, read at dyadic resolution
-- statement:
--   This file sets up the finite combinatorial model of Boolean tables from which a random one-periodic set is built by routing points down a finite tree. Fix $M, d \in \mathbb{N}$. For $b \in \mathbb{N}$ and $x \in \mathbb{R}$ let
--   $$
--   \kappa_b(x) = \big\lfloor 2^{b+2}\{x\} \big\rfloor \in \{0,1,\dots,2^{b+2}-1\}
--   $$
--   be the dyadic key of $x$, i.e. the index of the cell of mesh $2^{-(b+2)}$ containing the fractional part $\{x\} = x - \lfloor x \rfloor$. Boolean values are written $0$ (false) and $1$ (true).
--
--   1. **Children, nodes and leaves.** The child alphabet is $\{0,1,\dots,M\}$. The last child $M$ is the *default* child, and each of the $M$ other children $i \in \{0,\dots,M-1\}$ has its own selector. A *node* is a word $P$ over this alphabet of length $|P| < d$ (a vertex at which a decision is still made), and a *leaf* is a word of length exactly $d$. Write $\mathcal{N}_{M,d}$ and $\mathcal{L}_{M,d}$ for the finite sets of nodes and leaves.
--
--   2. **Addresses.** Given selector resolutions $b : \mathcal{N}_{M,d} \times \{0,\dots,M-1\} \to \mathbb{N}$, the set of selector addresses is
--   $$
--   \mathcal{A}^{\mathrm{sel}}_b = \big\{ ((P,i),j) : P \in \mathcal{N}_{M,d},\ 0 \le i < M,\ 0 \le j < 2^{b(P,i)+2} \big\}.
--   $$
--   Given terminal resolutions $c : \mathcal{L}_{M,d} \to \mathbb{N}$, the set of terminal addresses is $\mathcal{A}^{\mathrm{ter}}_c = \{ (L,j) : L \in \mathcal{L}_{M,d},\ 0 \le j < 2^{c(L)+2} \}$. Every address retains the name $(P,i)$ or $L$ of its table, so distinct tables never share a coordinate.
--
--   3. **Tables.** A selector table is a function $\omega : \mathcal{A}^{\mathrm{sel}}_b \to \{0,1\}$, and a terminal table is a function $\mathcal{A}^{\mathrm{ter}}_c \to \{0,1\}$.
--
--   4. **Reading the tables at a point.** For a node $P$, a selector index $i < M$ and $x \in \mathbb{R}$, the selector coordinate read at $x$ is $\alpha_b(P,i,x) = ((P,i), \kappa_{b(P,i)}(x))$; for a leaf $L$ the terminal coordinate is $\tau_c(L,x) = (L, \kappa_{c(L)}(x))$. The selector value is extended to all words $P$ over $\{0,\dots,M\}$ by
--   $$
--   s_\omega(P,i,x) = \begin{cases} \omega\big(\alpha_b(P,i,x)\big) & \text{if } |P| < d, \\ 0 & \text{otherwise}. \end{cases}
--   $$
--
--   The file also proves the basic facts used later: $s_\omega(P,i,x) = \omega(\alpha_b(P,i,x))$ for every node $P \in \mathcal{N}_{M,d}$; keys, coordinates and selector values are one-periodic in $x$, i.e. $\kappa_b(x+1) = \kappa_b(x)$, $\alpha_b(P,i,x+1) = \alpha_b(P,i,x)$, $\tau_c(L,x+1) = \tau_c(L,x)$ and $s_\omega(P,i,x+1) = s_\omega(P,i,x)$; and for each fixed $x$ the map $(P,i) \mapsto \alpha_b(P,i,x)$ is injective, so reading all selector tables at one centre consults pairwise distinct coordinates.
--
--   In the construction the selector and terminal tables are random with independent entries. Periodicity makes the resulting random set one-periodic, and the injectivity at a fixed centre is what allows the selector bits seen by a single point to be treated as independent fair coins.
--
--   **Formalization Note** Children are `Fin (M + 1)` with default `Fin.last M`; nodes are the subtype of `List (Fin (M + 1))` of length `< d`, leaves are `List.Vector (Fin (M + 1)) d`, and addresses are dependent pairs (`Sigma` types) with second component in `Fin (2 ^ (b + 2))`. These finite types carry the discrete measurable structure (`⊤`, with `DiscreteMeasurableSpace` instances), and a `Fintype` instance is constructed for the node type.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/FiniteTableModel.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/FiniteTableModel.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DyadicAvoidance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory

namespace Problem310.FiniteTableModel

/-- Child `M` is default and the other `M` children have selectors. -/
abbrev Child (M : ℕ) := Fin (M + 1)

/-- Nodes at which a depth-`d` router still makes a decision. -/
abbrev Node (M d : ℕ) := {P : List (Child M) // P.length < d}

/-- A terminal path. This is definitionally a list with the required length. -/
abbrev Leaf (M d : ℕ) := List.Vector (Child M) d

instance nodeFintype (M d : ℕ) : Fintype (Node M d) := by
  classical
  let f : (Σ k : Fin d, List.Vector (Child M) k.val) → Node M d :=
    fun p => ⟨p.2.val, by simpa only [p.2.property] using p.1.isLt⟩
  apply Fintype.ofSurjective f
  intro P
  exact ⟨⟨⟨P.val.length, P.property⟩, ⟨P.val, rfl⟩⟩, rfl⟩

instance nodeMeasurableSpace (M d : ℕ) : MeasurableSpace (Node M d) := ⊤
instance nodeDiscreteMeasurableSpace (M d : ℕ) : DiscreteMeasurableSpace (Node M d) := by constructor; intro s; trivial
instance leafMeasurableSpace (M d : ℕ) : MeasurableSpace (Leaf M d) := ⊤
instance leafDiscreteMeasurableSpace (M d : ℕ) : DiscreteMeasurableSpace (Leaf M d) := by constructor; intro s; trivial

/-- Finite selector-table addresses include the table name as well as its key. -/
abbrev SelectorAddress {M d : ℕ} (b : Node M d → Fin M → ℕ) :=
  Σ e : Node M d × Fin M, Fin (2 ^ (b e.1 e.2 + 2))

/-- Terminal addresses include the leaf name, preventing collisions between tables. -/
abbrev TerminalAddress {M d : ℕ} (b : Leaf M d → ℕ) :=
  Σ L : Leaf M d, Fin (2 ^ (b L + 2))

instance selectorAddressMeasurableSpace {M d : ℕ} (b : Node M d → Fin M → ℕ) :
    MeasurableSpace (SelectorAddress b) := ⊤
instance selectorAddressDiscreteMeasurableSpace {M d : ℕ} (b : Node M d → Fin M → ℕ) :
    DiscreteMeasurableSpace (SelectorAddress b) := by constructor; intro s; trivial
instance terminalAddressMeasurableSpace {M d : ℕ} (b : Leaf M d → ℕ) :
    MeasurableSpace (TerminalAddress b) := ⊤
instance terminalAddressDiscreteMeasurableSpace {M d : ℕ} (b : Leaf M d → ℕ) :
    DiscreteMeasurableSpace (TerminalAddress b) := by constructor; intro s; trivial

abbrev SelectorTable {M d : ℕ} (b : Node M d → Fin M → ℕ) := SelectorAddress b → Bool
abbrev TerminalTable {M d : ℕ} (b : Leaf M d → ℕ) := TerminalAddress b → Bool

/-- The center exposure consults exactly one deterministic coordinate per selector table. -/
def selectorAddress {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (P : Node M d) (i : Fin M) (x : ℝ) : SelectorAddress b :=
  ⟨(P, i), GridSeparation.dyadicKey (b P i) x⟩

/-- The terminal coordinate read along the selected leaf. -/
def terminalAddress {M d : ℕ} (b : Leaf M d → ℕ)
    (L : Leaf M d) (x : ℝ) : TerminalAddress b :=
  ⟨L, GridSeparation.dyadicKey (b L) x⟩

/-- Selector values are extended to all lists; routing uses only valid nodes. -/
def selectorValue {M d : ℕ} (b : Node M d → Fin M → ℕ) (ω : SelectorTable b)
    (P : List (Child M)) (i : Fin M) (x : ℝ) : Bool :=
  if h : P.length < d then ω (selectorAddress b ⟨P, h⟩ i x) else false

@[simp] theorem selectorValue_valid {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : Node M d) (i : Fin M) (x : ℝ) :
    selectorValue b ω P.val i x = ω (selectorAddress b P i x) := by
  simp [selectorValue, P.property]

lemma dyadicKey_add_one (b : ℕ) (x : ℝ) :
    GridSeparation.dyadicKey b (x + 1) = GridSeparation.dyadicKey b x := by
  apply (GridSeparation.dyadicKey_eq_iff _ _ _).mpr
  exact GridSeparation.periodicKey_add_one _ _

@[simp] lemma selectorAddress_add_one {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (P : Node M d) (i : Fin M) (x : ℝ) :
    selectorAddress b P i (x + 1) = selectorAddress b P i x := by
  simp [selectorAddress, dyadicKey_add_one]

@[simp] lemma terminalAddress_add_one {M d : ℕ} (b : Leaf M d → ℕ)
    (L : Leaf M d) (x : ℝ) :
    terminalAddress b L (x + 1) = terminalAddress b L x := by
  simp [terminalAddress, dyadicKey_add_one]

@[simp] lemma selectorValue_add_one {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : List (Child M)) (i : Fin M) (x : ℝ) :
    selectorValue b ω P i (x + 1) = selectorValue b ω P i x := by
  by_cases h : P.length < d <;> simp [selectorValue, h]

/-- Exposing the center reads distinct coordinates because table names are retained. -/
lemma center_selectorAddress_injective {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (x : ℝ) : Function.Injective (fun e : Node M d × Fin M => selectorAddress b e.1 e.2 x) := by
  intro e f h
  exact congrArg Sigma.fst h

end Problem310.FiniteTableModel

end

end OAI


