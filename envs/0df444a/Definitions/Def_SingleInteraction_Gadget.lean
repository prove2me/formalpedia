-- Prove2me | Definitions.Def_SingleInteraction_Gadget
-- name    : SingleInteraction_Gadget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:54:14.559134+00:00
-- url     : https://prove2.me/theorems/a1246f45-68a1-4843-a89f-21043ac536a2
-- title:
--   Parameters of the two-local gadget of §5.1.2
-- statement:
--   The gadget of §5.1.2 is specified by
--
--   1. $n$ work qubits and $M$ target occurrences $(u_e,v_e)$ with $u_e\ne v_e$ (repeats allowed);
--   2. two core registers $\mathcal A,\mathcal B$ of $S$ qubits each;
--   3. positive integers $R,L$ with $S\ge L$;
--   4. for each occurrence $e$, $R$ mediators anchored to $\mathcal A$ and $R$ anchored to $\mathcal B$, all distinct;
--   5. for each mediator $c$, an anchor set $\Gamma(c)$ of $L$ distinct qubits of its own core register (different mediators may share anchors).
--
--   The physical qubits are the work qubits, the core and the $2MR$ mediators.
--
--   **Formalization Note** A mediator is a triple (occurrence, register, copy). Every gadget statement holds for all choices allowed above.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.2, pp.56–57

import Mathlib

namespace SingleInteraction

/-- The parameters of the two-local gadget of §5.1.2 (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), pp.56–57).

* `n` work qubits and `M` target occurrences `occ e = (u_e, v_e)` with `u_e ≠ v_e` (the XY occurrence
  list `K = Σ_e K_{u_e v_e}` of Lemma 61; repeats allowed);
* core registers `𝒜`, `ℬ` of `S` qubits each;
* "Let `R, L` be positive integers, with `S ≥ L`" (p.56);
* for each occurrence `e`, `R` mediators anchored to `𝒜` and `R` anchored to `ℬ` (p.57): the mediator
  `c = (e, g, r)` is anchored to `𝒜` when `g = true` and to `ℬ` when `g = false`;
* the anchor set `Γ(c)` of mediator `c`, a set of `L` qubits of its own core register (indices in
  `Fin S`), "Different mediators may share anchor sites" (p.57).

**Formalization Note** The anchor sets are arbitrary subject to `|Γ(c)| = L`; every gadget statement holds
for all such choices. Mediators of different occurrences are distinct by construction (they are indexed
by the occurrence). The qubit types are `Gadget.Med` (mediators), `Gadget.Qb` (all physical qubits:
work, then core `𝒜 ⊕ ℬ`, then mediators) and `Gadget.VS` (work and mediators, the register of a core
sector). -/
structure Gadget where
  /-- number of work qubits -/
  n : ℕ
  /-- number of target occurrences -/
  M : ℕ
  /-- size of each core register -/
  S : ℕ
  /-- mediators per occurrence and core register -/
  R : ℕ
  /-- anchors per mediator -/
  L : ℕ
  /-- the occurrences `(u_e, v_e)` -/
  occ : Fin M → Fin n × Fin n
  occ_ne : ∀ e, (occ e).1 ≠ (occ e).2
  /-- the anchor set of each mediator, inside its own core register -/
  Γ : Fin M × Bool × Fin R → Finset (Fin S)
  card_Γ : ∀ c, (Γ c).card = L
  R_pos : 0 < R
  L_pos : 0 < L
  L_le_S : L ≤ S

namespace Gadget

/-- Mediator labels `(e, g, r)`: occurrence `e`, core register (`true` = `𝒜`, `false` = `ℬ`), copy `r`. -/
abbrev Med (G : Gadget) : Type := Fin G.M × Bool × Fin G.R

/-- All physical qubits: work qubits, then the core `𝒜 ⊕ ℬ`, then the mediators. -/
abbrev Qb (G : Gadget) : Type := Fin G.n ⊕ (Fin G.S ⊕ Fin G.S) ⊕ G.Med

/-- The work and mediator qubits, the register of a fixed core configuration. -/
abbrev VS (G : Gadget) : Type := Fin G.n ⊕ G.Med

/-- Work qubit `i`. -/
def work (G : Gadget) (i : Fin G.n) : G.Qb := Sum.inl i

/-- Core qubit `x` of `𝒜`. -/
def coreA (G : Gadget) (x : Fin G.S) : G.Qb := Sum.inr (Sum.inl (Sum.inl x))

/-- Core qubit `y` of `ℬ`. -/
def coreB (G : Gadget) (y : Fin G.S) : G.Qb := Sum.inr (Sum.inl (Sum.inr y))

/-- Mediator qubit `c`. -/
def med (G : Gadget) (c : G.Med) : G.Qb := Sum.inr (Sum.inr c)

/-- The core qubit with index `x` in the register of mediator `c`. -/
def anchor (G : Gadget) (c : G.Med) (x : Fin G.S) : G.Qb :=
  if c.2.1 then G.coreA x else G.coreB x

/-- The first endpoint `u(c)` of the occurrence of mediator `c`. -/
def u (G : Gadget) (c : G.Med) : Fin G.n := (G.occ c.1).1

/-- The second endpoint `v(c)` of the occurrence of mediator `c`. -/
def v (G : Gadget) (c : G.Med) : Fin G.n := (G.occ c.1).2

end Gadget

end SingleInteraction


