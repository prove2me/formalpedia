-- Prove2me | Definitions.Def_WildeQIT_QErasure_IsAntidegradable
-- name    : WildeQIT_QErasure_IsAntidegradable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:27.699829+00:00
-- url     : https://prove2.me/theorems/690ed13c-c795-4839-a8dd-02c05edd1987
-- title:
--   Antidegradable quantum channel
-- statement:
--   A quantum channel $\mathcal N_{A'\to B}$ is **antidegradable** if there exists a degrading channel $\mathcal D_{E\to B}$ such that
--
--   $$
--   \mathcal D_{E\to B}\big(\mathcal N^c_{A'\to E}(\rho_{A'})\big)=\mathcal N_{A'\to B}(\rho_{A'})
--   $$
--
--   for every input state $\rho_{A'}$, where $\mathcal N^c$ is a channel complementary to $\mathcal N$.
--
--   Eve can simulate Bob's output; such channels have zero quantum capacity.
--
--   **Formalization Note** $\mathcal N^c$ is the complementary channel of the canonical isometric extension; $\mathcal D$ is any channel in Kraus form out of the environment (which carries classical decidable equality); "every input state" ranges over density operators.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 13.5.3, (13.156), p. 412

import Definitions.Def_WildeQIT_Degradable_complementaryApply
import Definitions.Def_WildeQIT_IsDensityOperator

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 13.5.3 (Antidegradable
Quantum Channel), p. 412.
-/

open Matrix

namespace WildeQIT.QErasure

open Classical in
/-- **Definition 13.5.3 (Antidegradable Quantum Channel)** (Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, p. 412, eq. (13.156)): "A quantum channel `N_{A′→B}` is antidegradable if
there exists a degrading channel `D_{E→B}` such that `D_{E→B}(N^c_{A′→E}(ρ_{A′})) = N_{A′→B}(ρ_{A′})`
for any input state `ρ_{A′}` and where `N^c_{A′→E}` is a channel complementary to `N_{A′→B}`."

**Formalization Note.** The complementary channel is the one of the canonical isometric extension
(environment `N.ι`, `complementaryApply`); the degrading channel `D` is any quantum channel from that
environment to `B`, in Kraus form. As for degradability, the property does not depend on the choice of
complementary channel (two complementary channels are related by an isometry on the environment, or
its adjoint followed by a channel). "For any input state" is quantification over density operators.
The environment carries the classical decidable equality, needed only to form a channel out of it. -/
def IsAntidegradable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    (N : QChannel a b) : Prop :=
  ∃ D : QChannel N.ι b, ∀ ρ : Matrix a a ℂ, IsDensityOperator ρ →
    D.apply (WildeQIT.Degradable.complementaryApply N ρ) = N.apply ρ

end WildeQIT.QErasure


