-- Prove2me | Definitions.Def_MantriCVQ_CodeFamily
-- name    : MantriCVQ_CodeFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:42.581532+00:00
-- url     : https://prove2.me/theorems/31fcc51e-4234-4892-ab23-fa01efa267af
-- title:
--   Code families with exact quantum decoders
-- statement:
--   A **code family of degree $d$** over a gate set $G$ satisfies the degree condition and also: (i) $C_m(s,x)$ is computable in time polynomial in $m$, uniformly in $m$; (iii) a uniform family of unitaries $U_m$, implemented exactly together with their inverses by polynomial-size circuits over $G$, satisfies
--   $$U_m|C_s\rangle=|s\rangle,\qquad |C_s\rangle=2^{-m/2}\sum_{x\in\mathbb F_2^m}(-1)^{C_m(s,x)}|x\rangle.$$
--   Exact decoding gives the quantum algorithm and the honest prover, and it forces distinct codewords to have distance exactly $1/2$.
--
--   **Formalization Note** The circuits have no oracle gates and may use ancillas that start in and return to $|0\rangle$. All conditions are stated for positive multiples of eight only.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Definition 3.1, p. 15 (PDF p. 17)

import Mathlib
import Definitions.Def_MantriCVQ_CodeDeg
import Definitions.Def_MantriCVQ_Circ
import Definitions.Def_MantriCVQ_ket
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

/-- The phase state `|C_s⟩ = 2^{-m/2} ∑_x (-1)^{C_m(s,x)} |x⟩` tensored with `anc` ancillas in `|0⟩`
(Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Definition 3.1 (iii), p. 15 (PDF p. 17)). -/
noncomputable def phaseState (code : (m : ℕ) → Bits m → Bits m → Bool) (m anc : ℕ) (s : Bits m) :
    QState (m + anc) :=
  fun y =>
    if ∀ j : Fin anc, y (Fin.natAdd m j) = false then
      ((Real.sqrt 2 : ℂ) ^ m)⁻¹ *
        (if code m s (fun i => y (Fin.castAdd anc i)) then -1 else 1)
    else 0

/-- A code family of degree `d` over the gate set `G` (Mantri, arXiv:2610.37635 (PDF sha256
d1fab777…1d0b33), Definition 3.1, p. 15 (PDF p. 17)): the degree condition (ii) of `CodeDeg`, the
polynomial-time computability (i), and (iii) a uniform family of unitaries `U_m` implemented exactly,
together with their inverses, by polynomial-size circuits over `G`, with `U_m |C_s⟩ = |s⟩`.

**Formalization Note** The circuits have no oracle gates and may use ancillas, which start in and
return to `|0⟩`. `decInv` inverts `dec` on every state. All conditions are stated for positive
multiples `m` of eight only. -/
structure CodeFamily (G : List Gate) (d : ℕ) extends CodeDeg d where
  /-- (i): `(m, s, x) ↦ C_m(s, x)` is computable in polynomial time -/
  code_poly : ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ m : ℕ, 0 < m → 8 ∣ m → ∀ s x : Bits m,
    f (tup [unary m, List.ofFn s, List.ofFn x]) = [code m s x]
  /-- the ancilla count of the decoder -/
  anc : ℕ → ℕ
  /-- the circuit of `U_m` -/
  dec : (m : ℕ) → Circ G (m + anc m)
  /-- the circuit of `U_m⁻¹` -/
  decInv : (m : ℕ) → Circ G (m + anc m)
  no_oracle : ∀ m : ℕ, (dec m).queries = 0 ∧ (decInv m).queries = 0
  /-- (iii): uniformity -/
  dec_uniform : ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ m : ℕ, 0 < m → 8 ∣ m →
    f (unary m) = encNat (anc m) ++ encStr [(dec m).enc, (decInv m).enc]
  /-- (iii): polynomial size -/
  dec_poly : ∃ q : Polynomial ℕ, ∀ m : ℕ, 0 < m → 8 ∣ m →
    (dec m).size ≤ q.eval m ∧ (decInv m).size ≤ q.eval m ∧ anc m ≤ q.eval m
  /-- (iii): `U_m |C_s⟩ |0⟩ = |s⟩ |0⟩`, for every oracle since the circuit makes no query -/
  dec_spec : ∀ (m : ℕ), 0 < m → 8 ∣ m → ∀ (O : Oracle) (s : Bits m),
    (dec m).run O (phaseState code m (anc m) s) =
      ket _ (List.ofFn s ++ List.replicate (anc m) false)
  /-- (iii): `decInv` is the inverse of `dec`, on every state -/
  dec_inv : ∀ (m : ℕ), 0 < m → 8 ∣ m → ∀ (O : Oracle) (ψ : QState (m + anc m)),
    (decInv m).run O ((dec m).run O ψ) = ψ ∧ (dec m).run O ((decInv m).run O ψ) = ψ

end MantriCVQ


