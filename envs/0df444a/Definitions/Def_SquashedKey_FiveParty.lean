-- Prove2me | Definitions.Def_SquashedKey_FiveParty
-- name    : SquashedKey_FiveParty
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:29:52.15518+00:00
-- url     : https://prove2.me/theorems/24c56acc-915b-402a-878c-26423f81dda5
-- title:
--   The five registers $A A' B B' E$ and the conditional mutual informations of Lemma 1 and (32)–(33)
-- statement:
--   Alice holds a key system $A$ of dimension $K$ and a shield $A'$; Bob holds a key system $B$ of dimension $K$ and a shield $B'$; $E$ is an extending system. The shields and $E$ have arbitrary dimension. For an operator $\rho$ on $AA'BB'E$ this module defines, in bits:
--
--   1. $I(AA';BB'|E)_\rho$;
--   2. $I(A;BB'|E)_\rho$, on the marginal with $A'$ traced out;
--   3. $I(A';BB'|AE)_\rho$;
--   4. $I(A';B'|AE)_\rho$, on the marginal with $B$ traced out;
--   5. $I(A';B|AB'E)_\rho$ (written $I(A';B|B'AE)$ in (32)).
--
--   These are the five quantities in Lemma 1 (31) and the identities (32)–(33) (p.7), and in (48)–(51) of the proof of Theorem 2 (p.9).
--
--   **Formalization Note** A basis index is $(((a,s),(b,t)),e)$ with $a,b\in\{0,\dots,K-1\}$, $s\in A'$, $t\in B'$, $e\in E$. Each quantity is the extended conditional mutual information of the marginal obtained by an explicit relabelling of these indices (an equivalence of index types, given in the code) followed by the partial trace over the discarded registers. The conditioning system of item 5 is grouped as $(A,B'),E$.
-- source:
--   Wilde, Squashed entanglement and approximate private states, arXiv:1606.08028v3, Lemma 1 (31) and (32)–(34), p.7; (48)–(51), p.9

import Mathlib
import Definitions.Def_SquashedKey_Information

open scoped ENNReal

namespace SquashedKey

/-- **The registers of an extension of a bipartite state with key and shield systems**,
Wilde, *Squashed entanglement and approximate private states*, arXiv:1606.08028v3, §2.3, p.4, and
Lemma 1, p.7: Alice holds the key system `A` and the shield `A′`, Bob holds the key system `B` and
the shield `B′`, and `E` is an extending (or purifying) system.

**Formalization Note** A basis index is `(((a, s), (b, t)), e)` with `a : Fin K` (system `A`),
`s : A′`, `b : Fin K` (system `B`), `t : B′` and `e : E`; the Hilbert space of each system is
`ℓ²` of its index type. Alice's side `AA′` is `Fin K × A′` and Bob's side `BB′` is `Fin K × B′`.
The key systems have dimension `K`; `A′`, `B′` and `E` are arbitrary types. -/
abbrev FiveParty (K : ℕ) (A' B' E : Type) := ((Fin K × A') × (Fin K × B')) × E

/-- Registers grouped as `A ; BB′ | E`, with `A′` discarded: the index `(((a,s),(b,t)),e)` goes
to `(((a, (b,t)), e), s)`. Used for `I(A; BB′|E)`, arXiv:1606.08028v3, (31), p.7. -/
def regroupA_BBp_E (K : ℕ) (A' B' E : Type) :
    FiveParty K A' B' E ≃ ((Fin K × (Fin K × B')) × E) × A' where
  toFun x := (((x.1.1.1, x.1.2), x.2), x.1.1.2)
  invFun y := (((y.1.1.1, y.2), y.1.1.2), y.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Registers grouped as `A′ ; BB′ | AE`, nothing discarded: `(((a,s),(b,t)),e)` goes to
`(((s, (b,t)), (a, e)), ())`. Used for `I(A′; BB′|AE)`, arXiv:1606.08028v3, (32), p.7. -/
def regroupAp_BBp_AE (K : ℕ) (A' B' E : Type) :
    FiveParty K A' B' E ≃ ((A' × (Fin K × B')) × (Fin K × E)) × Unit where
  toFun x := (((x.1.1.2, x.1.2), (x.1.1.1, x.2)), ())
  invFun y := (((y.1.2.1, y.1.1.1), y.1.1.2), y.1.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Registers grouped as `A′ ; B′ | AE`, with `B` discarded: `(((a,s),(b,t)),e)` goes to
`(((s, t), (a, e)), b)`. Used for `I(A′; B′|AE)`, arXiv:1606.08028v3, (32)–(33), p.7. -/
def regroupAp_Bp_AE (K : ℕ) (A' B' E : Type) :
    FiveParty K A' B' E ≃ ((A' × B') × (Fin K × E)) × Fin K where
  toFun x := (((x.1.1.2, x.1.2.2), (x.1.1.1, x.2)), x.1.2.1)
  invFun y := (((y.1.2.1, y.1.1.1), (y.2, y.1.1.2)), y.1.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Registers grouped as `A′ ; B | AB′E`, nothing discarded: `(((a,s),(b,t)),e)` goes to
`(((s, b), ((a, t), e)), ())`. Used for `I(A′; B|AB′E)` (31), p.7, which (32) writes
`I(A′; B|B′AE)`. -/
def regroupAp_B_ABpE (K : ℕ) (A' B' E : Type) :
    FiveParty K A' B' E ≃ ((A' × Fin K) × ((Fin K × B') × E)) × Unit where
  toFun x := (((x.1.1.2, x.1.2.1), ((x.1.1.1, x.1.2.2), x.2)), ())
  invFun y := (((y.1.2.1.1, y.1.1.1), (y.1.1.2, y.1.2.1.2)), y.1.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- `I(AA′; BB′|E)` in bits, arXiv:1606.08028v3, (32)–(34), p.7, of an operator on
`(AA′)(BB′)E`: the conditional mutual information (15) with `X = AA′`, `Y = BB′`, `Z = E`. -/
noncomputable def infoAAp_BBp_E {K : ℕ} {A' B' E : Type}
    (ρ : Matrix (FiveParty K A' B' E) (FiveParty K A' B' E) ℂ) : ℝ≥0∞ :=
  cmiBits ρ

/-- `I(A; BB′|E)` in bits, arXiv:1606.08028v3, (31)–(32), p.7: the conditional mutual
information (15) of the marginal on `ABB′E` (the shield `A′` traced out), with `X = A`, `Y = BB′`,
`Z = E`. -/
noncomputable def infoA_BBp_E {K : ℕ} {A' B' E : Type}
    (ρ : Matrix (FiveParty K A' B' E) (FiveParty K A' B' E) ℂ) : ℝ≥0∞ :=
  cmiOf (regroupA_BBp_E K A' B' E) ρ

/-- `I(A′; BB′|AE)` in bits, arXiv:1606.08028v3, (32), p.7: the conditional mutual information
(15) with `X = A′`, `Y = BB′`, `Z = AE`. -/
noncomputable def infoAp_BBp_AE {K : ℕ} {A' B' E : Type}
    (ρ : Matrix (FiveParty K A' B' E) (FiveParty K A' B' E) ℂ) : ℝ≥0∞ :=
  cmiOf (regroupAp_BBp_AE K A' B' E) ρ

/-- `I(A′; B′|AE)` in bits, arXiv:1606.08028v3, (32)–(33), p.7: the conditional mutual
information (15) of the marginal on `AA′B′E` (the key system `B` traced out), with `X = A′`,
`Y = B′`, `Z = AE`. -/
noncomputable def infoAp_Bp_AE {K : ℕ} {A' B' E : Type}
    (ρ : Matrix (FiveParty K A' B' E) (FiveParty K A' B' E) ℂ) : ℝ≥0∞ :=
  cmiOf (regroupAp_Bp_AE K A' B' E) ρ

/-- `I(A′; B|AB′E)` in bits, arXiv:1606.08028v3, (31), p.7 (written `I(A′; B|B′AE)` in (32)):
the conditional mutual information (15) with `X = A′`, `Y = B`, `Z = AB′E`.

**Formalization Note** The conditioning system is grouped as `(A, B′), E`. The order of the
conditioning registers does not change the quantity in the paper; the Lean statements use this one
grouping for both (31) and (32). -/
noncomputable def infoAp_B_ABpE {K : ℕ} {A' B' E : Type}
    (ρ : Matrix (FiveParty K A' B' E) (FiveParty K A' B' E) ℂ) : ℝ≥0∞ :=
  cmiOf (regroupAp_B_ABpE K A' B' E) ρ

end SquashedKey


