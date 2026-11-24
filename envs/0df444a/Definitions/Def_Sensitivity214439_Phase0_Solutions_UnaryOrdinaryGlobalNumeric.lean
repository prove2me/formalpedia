-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryOrdinaryGlobalNumeric
-- name    : Sensitivity214439_Phase0_Solutions_UnaryOrdinaryGlobalNumeric
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:49:04.416386+00:00
-- url     : https://prove2.me/theorems/4828660b-981c-401f-9195-ff0da8d9ec33
-- title:
--   Finite population states and price checking for ordinary unary gains
-- statement:
--   The ordinary price record has low, high, marked, external, and internal components. Price validity bounds the necessary child gain and loss entries: low $A(5,7)$, external $B(5,5)$, high gains from heights $6,7$, their marked gain-plus-loss sums, and internal losses from heights above $7$.
--
--   A state records target count $t$, guard-head count $g$, and external-donor count $e$. Put $I=\binom g2$, $O=g(q+1)-I$, $H=t+g$, and $a=H+e$. Validity is the conjunction
--   $$
--   \binom H2\le qt+(q+1)g,\quad
--   e\le qt+(q+1)g-\binom H2,\quad
--   g(q+1)\le I+gt+ge.
--   $$
--   The finite state list has $t\le2q+1$, $g\le2q+3$ when guard heads are enabled and $g=0$ otherwise, and $e\le O$.
--
--   The low population cap uses the specified Paley incoming-prefix table, the trivial bound $2659-a$ when $a\le q$, and the special cap $1352$ for a three-target directed triangle at $q=1$. The scalar fee is
--   $$
--   tp_{\rm high}+\min(t,O-e)(p_{\rm marked}-p_{\rm high})
--   +\min(g,I)p_{\rm internal}+ep_{\rm external}
--   +\operatorname{population}(q,s)p_{\rm low}.
--   $$
--   The checker requires every valid enumerated state to have a supported population cap and fee at most the proposed bound.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryOrdinaryGlobalNumeric.lean lines 11–96; SHA256 7744d0cc81374ec649af5ddf0b96765ab9ea2b5a2143c050b42d064a46f2fcec; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_PaleyUnary_Data
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic

namespace SensitivityLocalNumeric
end SensitivityLocalNumeric
namespace SensitivityUnaryOrdinaryGlobalNumeric
end SensitivityUnaryOrdinaryGlobalNumeric



/-! A direct finite certificate for ordinary unary global gains.  The states
record target heads, guard heads, and distinct donors outside those heads. -/
namespace SensitivityUnaryOrdinaryGlobalNumeric

open SensitivityLocalNumeric

structure Prices where
  low : ℕ
  high : ℕ
  marked : ℕ
  external : ℕ
  internal : ℕ

def PriceValid (input : Array ℕ) (p : Prices) : Prop :=
  entry input 0 5 7 ≤ p.low ∧ entry input 1 5 5 ≤ p.external ∧ p.high ≤ p.marked ∧
  (∀ h : Fin 13, 5 < h.val → h.val ≤ 7 →
    entry input 0 h.val 7 ≤ p.high ∧
      entry input 0 h.val 7 + entry input 2 5 (h.val-1) ≤ p.marked) ∧
  (∀ h : Fin 13, 7 < h.val → entry input 2 5 (h.val-1) ≤ p.internal)

instance (input : Array ℕ) (p : Prices) : Decidable (PriceValid input p) := by
  unfold PriceValid
  infer_instance

structure State where
  targets : ℕ
  guards : ℕ
  external : ℕ

def inside (s : State) : ℕ := s.guards.choose 2
def outside (q : ℕ) (s : State) : ℕ := s.guards*(q+1)-inside s
def heads (s : State) : ℕ := s.targets+s.guards
def active (s : State) : ℕ := heads s+s.external

def Valid (q : ℕ) (s : State) : Prop :=
  (heads s).choose 2 ≤ q*s.targets+(q+1)*s.guards ∧
  s.external ≤ q*s.targets+(q+1)*s.guards-(heads s).choose 2 ∧
  s.guards*(q+1) ≤ inside s+s.guards*s.targets+s.guards*s.external

instance (q : ℕ) (s : State) : Decidable (Valid q s) := by
  unfold Valid
  infer_instance

def states (q : ℕ) (guardEnabled : Bool) : List State :=
  (List.range (2*q+2)).flatMap fun t =>
    (List.range (if guardEnabled then 2*q+4 else 1)).flatMap fun g =>
      (List.range (g*(q+1)-g.choose 2+1)).map fun e => ⟨t,g,e⟩



def prefixBound (h f : ℕ) : ℕ :=
  if h ≤ f then 2659-h else
    ((PaleyWeil.paleyUnaryPrefixRows.find? fun r => r.1 == h && r.2.1 == f).getD (0,0,0)).2.2

def cyclicCase (q : ℕ) (s : State) : Prop :=
  q = 1 ∧ s.targets = 3 ∧ s.guards = 0 ∧ s.external = 0

instance (q : ℕ) (s : State) : Decidable (cyclicCase q s) := by
  unfold cyclicCase
  infer_instance

def population (q : ℕ) (s : State) : ℕ :=
  if cyclicCase q s then 1352 else prefixBound (active s) q

def Supported (q : ℕ) (s : State) : Prop :=
  cyclicCase q s ∨ active s ≤ q ∨
    (active s,q,population q s) ∈ PaleyWeil.paleyUnaryPrefixRows

instance (q : ℕ) (s : State) : Decidable (Supported q s) := by
  unfold Supported
  infer_instance

def fee (q : ℕ) (p : Prices) (s : State) : ℕ :=
  s.targets*p.high + min s.targets (outside q s-s.external)*(p.marked-p.high) +
    min s.guards (inside s)*p.internal + s.external*p.external + population q s*p.low

def check (q : ℕ) (enabled : Bool) (p : Prices) (bound : ℕ) : Bool :=
  (states q enabled).all fun s => decide (Valid q s → Supported q s ∧ fee q p s ≤ bound)






end SensitivityUnaryOrdinaryGlobalNumeric


