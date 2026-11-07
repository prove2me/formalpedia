-- Prove2me | Definitions.Def_LaconicBarrier_IOScheme_source
-- name    : LaconicBarrier_IOScheme_source
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:51.66789+00:00
-- url     : https://prove2.me/theorems/9b974427-d43c-4b7f-a26b-fb7a4f62027b
-- title:
--   The iO security game and its admissible index set
-- statement:
--   The public index is the code of a pair $(C_0, C_1)$ of circuits with the same number of inputs. The **admissible index set** consists of the codes of pairs with the same number of gates that are functionally equivalent. The challenger chooses $b \leftarrow \{0,1\}$, sends (the description of) $i\mathcal O(1^\lambda, C_b)$ and wins precisely when the reply equals $b$; the baseline is $1/2$. Circuit equivalence is imposed through the admissible index set and is not checked by the challenger.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.11, p.20; §7.1, p.46

import Mathlib
import Definitions.Def_LaconicBarrier_IOScheme
import Definitions.Def_LaconicBarrier_TwoMsg

namespace LaconicBarrier

open KarpLiptonOM

/-- The public index of the iO game: the tuple `(1ⁿ, 1^s, code of C₀, code of C₁)` of two circuits
with `n` inputs, coded with `s = |C₀|` gates. -/
def pairCode {n : ℕ} (C₀ C₁ : Circuit n) : List Bool :=
  QAdvFew.PoQOracle.tup [unary n, unary C₀.gates.length, circuitCode n C₀.gates.length C₀,
    circuitCode n C₀.gates.length C₁]

/-- The **admissible index set** of the iO game (Jain, Mathialagan, Roy, STOC 2027 submission
(manuscript sha256 1af78662…), §4.1.5, p.20: "the set of pairs of functionally equivalent circuits of
equal size and equal input length"; §7.1, p.46): codes of pairs `(C₀, C₁)` with the same number of
inputs and of gates that agree on every input. -/
def IOScheme.admissible : Set (List Bool) :=
  {x | ∃ (n : ℕ) (C₀ C₁ : Circuit n), C₀.gates.length = C₁.gates.length ∧
    (∀ u : List Bool, u.length = n → C₀.eval u = C₁.eval u) ∧ x = pairCode C₀ C₁}

open Classical in
/-- The pair coded by an index (any fixed pair when the index codes no equal-size pair). -/
noncomputable def decodePair (x : List Bool) : Σ n, Circuit n × Circuit n :=
  if h : ∃ p : Σ n, Circuit n × Circuit n,
      p.2.1.gates.length = p.2.2.gates.length ∧ pairCode p.2.1 p.2.2 = x
  then Classical.choose h else ⟨0, ⟨[], by simp⟩, ⟨[], by simp⟩⟩

/-- The **iO security game** as a family of two-message games indexed by the pair (Jain,
Mathialagan, Roy, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.11, p.20 and
§7.1, p.46: "The challenger chooses `b ← {0, 1}`, sends an obfuscation of `C_b`, and outputs `win`
precisely when the adversary's reply equals `b`; the baseline is `1/2`. Circuit equivalence is
imposed through the admissible index set"). The first coin is `b`, the others are the obfuscator's;
the challenge is the description of `iO(1^λ, C_b)`. -/
noncomputable def IOScheme.source (O : IOScheme) : TwoMsg where
  coins lam x := O.coins lam (decodePair x).1 (decodePair x).2.1.gates.length + 1
  chal lam x ρ := circCode (O.obf lam (decodePair x).1 (decodePair x).2.1.gates.length
    (if ρ 0 then (decodePair x).2.2 else (decodePair x).2.1) (fun i => ρ i.succ))
  wins lam x ρ a := decide (a = [ρ 0])
  c₀ := 1 / 2
  c₀_nonneg := by norm_num
  c₀_lt_one := by norm_num

end LaconicBarrier


