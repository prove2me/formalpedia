-- Prove2me | Definitions.Def_PricingWithTips3DM_6b7a275bb9cec4f884d54bad
-- name    : PricingWithTips3DM_6b7a275bb9cec4f884d54bad
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:19:41.666335+00:00
-- url     : https://prove2.me/theorems/8efe01dd-30d7-454e-92ba-0486d08fbfd1
-- title:
--   PricingWithTips 3DM dependency: HardnessReductions.Logic.Nae3Sat
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/DominikPeters/HardnessReductionsLean

import Definitions.Def_PricingWithTips3DM_559a735c0442b6eef1922892
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# NOT-ALL-EQUAL 3SAT

Satisfaction with a second demand: an assignment must not only make some
literal of each clause true, it must also leave some literal of each clause
false. Garey–Johnson's [LO3]. In the modern literature it is the source of
choice for MAX CUT, "not all equal" being literally a cut condition — though
that construction needs parallel edges, so this catalog reaches SIMPLE MAX
CUT by Garey–Johnson–Stockmeyer's original route through MAX 2SAT instead,
and NAE3SAT's natural descendant here is SET SPLITTING [SP4].

Not-all-equal satisfaction has one structural property that plain satisfaction
lacks, and every reduction from it or into it turns on it: it is invariant
under **complementing** the assignment (`CNF.naeSat_not`). Flipping every
variable exchanges the two demands, which are symmetric, so solutions come in
pairs. That is what lets a reduction fix the value of a distinguished variable
without loss of generality (`CNF.exists_naeSat_eq_false`), and it is why a
gadget can use one global variable as a stand-in for the constant `false`.

The width restriction here is `= 3`, where 3SAT's is `≤ 3`. The difference is
not an oversight: both entries state the sharpest restriction their hardness
proof actually delivers. Clause splitting keeps narrow clauses as they are, so
`SAT3` can only claim `≤ 3`; the gadget of `Nae3Sat/FromSat3.lean` emits
clauses of exactly three literals, so `NAE_SAT3` claims `= 3` — which is both
Garey–Johnson's statement and what the descendants will want.

Hardness proof (in `Nae3Sat/`): from 3SAT (`FromSat3.lean`, one fresh variable
per clause plus one global variable; certified in `FromSat3/Code.lean` and
`FromSat3/Adequacy.lean`).
-/

namespace Hardness

variable {V W : Type*}

/-! ### Not-all-equal satisfaction -/

/-- A clause is *not-all-equal satisfied* when some literal in it holds **and**
some literal in it fails. Note what this says about short clauses: a clause of
fewer than two literals can never be not-all-equal satisfied, the two demands
having no room to be met at once. -/
def Clause.Nae (σ : V → Bool) (c : Clause V) : Prop :=
  (∃ l ∈ c, l.Holds σ) ∧ ∃ l ∈ c, ¬l.Holds σ

/-- Not-all-equal satisfaction is stronger than satisfaction: it is the
positive demand plus a negative one. -/
theorem Clause.Nae.sat {σ : V → Bool} {c : Clause V} (h : Clause.Nae σ c) :
    Clause.Sat σ c := h.1

/-- **The symmetry**: complementing the assignment preserves not-all-equal
satisfaction, because it merely exchanges the two demands. -/
theorem Clause.nae_not {σ : V → Bool} {c : Clause V} (h : Clause.Nae σ c) :
    Clause.Nae (fun v ↦ !σ v) c := by
  obtain ⟨⟨l, hl, hh⟩, ⟨l', hl', hh'⟩⟩ := h
  exact ⟨⟨l', hl', Literal.holds_not.mpr hh'⟩,
    ⟨l, hl, fun hc ↦ Literal.holds_not.mp hc hh⟩⟩

/-- Not-all-equal satisfaction of a clause only depends on the assignment's
values at the variables of the clause. -/
theorem Clause.nae_congr {c : Clause V} {τ τ' : V → Bool}
    (h : ∀ l ∈ c, τ l.var = τ' l.var) : Clause.Nae τ c ↔ Clause.Nae τ' c :=
  and_congr (Clause.sat_congr h)
    ⟨fun ⟨l, hl, hh⟩ ↦ ⟨l, hl, fun hc ↦ hh ((Literal.holds_congr (h l hl)).mpr hc)⟩,
      fun ⟨l, hl, hh⟩ ↦ ⟨l, hl, fun hc ↦ hh ((Literal.holds_congr (h l hl)).mp hc)⟩⟩

/-- A formula is not-all-equal satisfied if every clause is. -/
def CNF.NaeSat (σ : V → Bool) (φ : CNF V) : Prop :=
  ∀ c ∈ φ, c.Nae σ

/-- A formula is not-all-equal satisfiable if some assignment does it. -/
def CNF.NaeSatisfiable (φ : CNF V) : Prop :=
  ∃ σ : V → Bool, φ.NaeSat σ

/-- The symmetry, at the level of formulas: solutions come in complementary
pairs. -/
theorem CNF.naeSat_not {σ : V → Bool} {φ : CNF V} (h : φ.NaeSat σ) :
    φ.NaeSat (fun v ↦ !σ v) :=
  fun c hc ↦ Clause.nae_not (h c hc)

/-- **Fixing a variable without loss of generality**: a not-all-equal
satisfiable formula has a solution giving any prescribed variable the value
`false` — complement the one it has if need be. This is what lets a gadget
treat a distinguished variable as the constant `false`, and it is used in both
directions of every reduction into a not-all-equal problem. -/
theorem CNF.exists_naeSat_eq_false {φ : CNF V} (h : φ.NaeSatisfiable) (v₀ : V) :
    ∃ σ : V → Bool, φ.NaeSat σ ∧ σ v₀ = false := by
  obtain ⟨σ, hσ⟩ := h
  cases hv : σ v₀
  · exact ⟨σ, hσ, hv⟩
  · exact ⟨fun v ↦ !σ v, CNF.naeSat_not hσ, by simp [hv]⟩

/-! ### Relabeling

Not-all-equal satisfiability is transported by exactly the same argument as
satisfiability, both directions passing through
`CNF.exists_relabel_assignment`: a labelling that separates the occurring
variables carries assignments both ways, and `Literal.holds_relabel` then
matches the two demands literal by literal. -/

/-- Relabeling preserves and reflects not-all-equal satisfiability as soon as
the map is injective *on the variables that occur*. The form the representation
theorem needs; gadget certificates use the corollary
`CNF.naeSatisfiable_relabel`. -/
theorem CNF.naeSatisfiable_relabel_of_injOn {f : V → W} {φ : CNF V}
    (hf : Set.InjOn f φ.vars) :
    (φ.relabel f).NaeSatisfiable ↔ φ.NaeSatisfiable := by
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨fun v ↦ τ (f v), fun c hc ↦ ?_⟩
    obtain ⟨⟨l, hl, hh⟩, ⟨l', hl', hh'⟩⟩ :=
      hτ (c.map (Literal.relabel f)) (List.mem_map_of_mem hc)
    obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hl
    obtain ⟨l₀', hl₀', rfl⟩ := List.mem_map.mp hl'
    exact ⟨⟨l₀, hl₀, hh⟩, ⟨l₀', hl₀', hh'⟩⟩
  · rintro ⟨σ, hσ⟩
    obtain ⟨τ, hτ⟩ := CNF.exists_relabel_assignment hf σ
    refine ⟨τ, fun c hc ↦ ?_⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    obtain ⟨⟨l, hl, hh⟩, ⟨l', hl', hh'⟩⟩ := hσ d hd
    exact ⟨⟨l.relabel f, List.mem_map_of_mem hl,
        (Literal.holds_relabel (hτ l.var (CNF.mem_vars hd hl))).mpr hh⟩,
      ⟨l'.relabel f, List.mem_map_of_mem hl',
        fun hc ↦ hh' ((Literal.holds_relabel
          (hτ l'.var (CNF.mem_vars hd hl'))).mp hc)⟩⟩

/-- Relabeling along an *injective* map preserves and reflects not-all-equal
satisfiability: the corollary gadget certificates use, their naming maps being
injective on all of `V`. -/
theorem CNF.naeSatisfiable_relabel {f : V → W} (hf : Function.Injective f)
    (φ : CNF V) : (φ.relabel f).NaeSatisfiable ↔ φ.NaeSatisfiable :=
  CNF.naeSatisfiable_relabel_of_injOn hf.injOn

/-! ### The problems -/

/-- NAE-SAT: is the formula not-all-equal satisfiable? Not a catalog entry of
its own — Garey–Johnson lists only the width-3 version, and this is here to be
restricted. -/
def NAE_SAT : Problem SatInstance := fun x ↦ x.φ.NaeSatisfiable

/-- NOT-ALL-EQUAL 3SAT: is the formula not-all-equal satisfiable, all its
clauses having exactly three literals? In the promise-free formulation of
`Problem.restrict` — a formula with a clause of another width is simply a
no-instance. -/
def NAE_SAT3 : Problem SatInstance :=
  NAE_SAT.restrict fun x ↦ ∀ c ∈ x.φ, c.length = 3

end Hardness


