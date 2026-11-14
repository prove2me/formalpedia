-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pi
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:43:48.905038+00:00
-- url     : https://prove2.me/theorems/b8d252fd-33b9-413c-b3b7-30cc04063e13
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pi — Encodings of fixed finite tables
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pi` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A function on a fixed finite index type is stored as a framed list of all its values. Values may
--   have unbounded encodings, such as words or tapes. Every entry and its framing contribute to size.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.encPi`: store a finite family in a fixed index order.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.length_encPi_le`: bound the whole table from the sizes of its entries.
--
--   ### References
--
--   Adapts Computability/Probabilistic/Pi.lean on the cslib `crypto` branch at
--   `5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing framed list encoding.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pi`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Pi.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.OfFn
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List_Size

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pi` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Encodings of fixed finite tables

A function on a fixed finite index type is stored as a framed list of all its values. Values may
have unbounded encodings, such as words or tapes. Every entry and its framing contribute to size.

## Main definitions

* `Turing.MultiTapeTM.encPi`: store a finite family in a fixed index order.

## Main results

* `Turing.MultiTapeTM.length_encPi_le`: bound the whole table from the sizes of its entries.

## References

Adapts Computability/Probabilistic/Pi.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing framed list encoding.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {Index Value : Type} [Fintype Index]

/-- Encode a family by listing every entry in a fixed order, independently of runtime inputs. -/
noncomputable def encPi (enc : Value ↪ List Bool) : (Index → Value) ↪ List Bool where
  toFun values := encList enc (List.ofFn (fun i => values ((Fintype.equivFin Index).symm i)))
  inj' := by
    intro values others h
    have heq := List.ofFn_injective ((encList enc).injective h)
    funext i
    simpa using congrFun heq (Fintype.equivFin Index i)

@[simp] theorem encPi_apply (enc : Value ↪ List Bool) (values : Index → Value) :
    encPi enc values = encList enc
      (List.ofFn (fun i => values ((Fintype.equivFin Index).symm i))) := rfl

/-- The table encoding charges every entry, including its list framing. -/
theorem length_encPi_le (enc : Value ↪ List Bool) (values : Index → Value)
    {bound : ℕ} (hbound : ∀ i, (enc (values i)).length ≤ bound) :
    (encPi enc values).length ≤ Fintype.card Index * (2 * bound + 1) := by
  simpa only [encPi_apply, List.length_ofFn] using length_encList_le enc
    (List.ofFn (fun i => values ((Fintype.equivFin Index).symm i)))
    (fun value hvalue => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hvalue; exact hbound _)

end Turing.MultiTapeTM


