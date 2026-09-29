-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
-- name    : LanglandsTunnell_CubicInduction_Congruence
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/39122103-7796-5760-aba4-ec50e6fa11d0
-- title:
--   Bottom-row congruence conditions inside the local maximal compact of GL₃
-- statement:
--   Throughout, $R$ is a Dedekind domain with field of fractions $K$ and $v$ is a height-one prime of $R$, so that $K_v$ denotes the $v$-adic completion of $K$, with its valuation taking values in $\mathbb{Z}^{\mathrm{m}}\cup\{0\}$ written multiplicatively. Recall that `localMaximalCompact3 R K v` is the subgroup of $\mathrm{GL}_3(K_v)$ consisting of those $k$ all of whose matrix entries, and all of whose entries of $k^{-1}$, have valuation $\le 1$.
--
--   For a natural number $c$, `congruenceK1 R K v c` is defined as the set of $k \in \mathrm{GL}_3(K_v)$ which lie in `localMaximalCompact3 R K v` and whose bottom row satisfies the three valuation inequalities
--   $$\mathrm{v}(k_{2,0}) \le q^{-c},\qquad \mathrm{v}(k_{2,1}) \le q^{-c},\qquad \mathrm{v}(k_{2,2}-1) \le q^{-c},$$
--   the bound being `WithZero.exp (-(c : ℤ))`; that is, the last row of $k$ is congruent to $(0,0,1)$ modulo $\mathfrak{p}_v^{c}$. Only the entries of $k$ itself, not those of $k^{-1}$, are constrained beyond membership in the maximal compact. This is a `Set`, not a `Subgroup`: no group law is asserted here.
--
--   The accompanying lemmas record that membership unfolds to exactly this conjunction; that membership implies membership in `localMaximalCompact3 R K v`; that the family is antitone, $c \le c'$ giving `congruenceK1 R K v c' ⊆ congruenceK1 R K v c`; and that the identity matrix lies in `congruenceK1 R K v c` for every $c$.
--
--   **Relation to Mathlib.** Mathlib's congruence subgroups are those of $\mathrm{SL}_2(\mathbb{Z})$; the local congruence conditions on $\mathrm{GL}_3$ over a $v$-adic completion defined here are the project's own.
--
--   **Where it is used.** These local level conditions belong to the $\mathrm{GL}_3$ framework used for the cubic induction in the Langlands–Tunnell step, which supplies the modularity of the residual mod-$3$ representation at the start of the Frey–Serre–Ribet–Wiles–Taylor–Wiles argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_Congruence.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Congruence

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

def congruenceK1 (c : ℕ) : Set (GL (Fin 3) (v.adicCompletion K)) :=
  {k | k ∈ localMaximalCompact3 R K v ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 0) ≤ WithZero.exp (-(c : ℤ)) ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 1) ≤ WithZero.exp (-(c : ℤ)) ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 2 - 1) ≤ WithZero.exp (-(c : ℤ))}

theorem mem_congruenceK1_iff {c : ℕ} {k : GL (Fin 3) (v.adicCompletion K)} :
    k ∈ congruenceK1 R K v c ↔
      k ∈ localMaximalCompact3 R K v ∧
      Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 0) ≤ WithZero.exp (-(c : ℤ)) ∧
      Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 1) ≤ WithZero.exp (-(c : ℤ)) ∧
      Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 2 - 1) ≤ WithZero.exp (-(c : ℤ)) :=
  Iff.rfl

theorem mem_localMaximalCompact3_of_mem_congruenceK1 {c : ℕ} {k : GL (Fin 3) (v.adicCompletion K)}
    (hk : k ∈ congruenceK1 R K v c) : k ∈ localMaximalCompact3 R K v :=
  hk.1

theorem congruenceK1_antitone {c c' : ℕ} (h : c ≤ c') :
    congruenceK1 R K v c' ⊆ congruenceK1 R K v c := by
  intro k hk
  obtain ⟨h0, h1, h2, h3⟩ := hk
  have hle : WithZero.exp (-(c' : ℤ)) ≤ WithZero.exp (-(c : ℤ)) :=
    WithZero.exp_le_exp.mpr (by omega)
  exact ⟨h0, h1.trans hle, h2.trans hle, h3.trans hle⟩

theorem one_mem_congruenceK1 (c : ℕ) : (1 : GL (Fin 3) (v.adicCompletion K)) ∈ congruenceK1 R K v c := by
  refine ⟨one_mem _, ?_, ?_, ?_⟩ <;> simp

end Congruence

end LanglandsTunnell.CubicInduction


