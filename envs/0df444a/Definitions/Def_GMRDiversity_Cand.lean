-- Prove2me | Definitions.Def_GMRDiversity_Cand
-- name    : GMRDiversity_Cand
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:38:16.408751+00:00
-- url     : https://prove2.me/theorems/a96be097-381a-4f25-a7ab-e05c15ad281d
-- title:
--   Candidates $(a,b)\in\{0,1\}^n\times\{0,1\}$, generation $\mathrm{Gen}_x$ and utility $U_x$ of the parity instance $\mathfrak G^{\mathrm{par}}_x$
-- statement:
--   Fix a hidden target $x\in\{0,1\}^n$. The parity-learning instance $\mathfrak G^{\mathrm{par}}_x$ has candidate space
--   $$
--   X:=\{0,1\}^n\times\{0,1\},
--   $$
--   and a candidate $(a,b)$ is read as the linear equation $a\cdot x=b$ over $\mathbb F_2$. Its two operators are:
--
--   1. **Generation** $\mathrm{Gen}_x()$ returns $(a,b)$ with $a\sim\mathrm{Unif}(\{0,1\}^n)$ and $b=a\cdot x \bmod 2$;
--   2. **Recombination** $\mathrm{XOR}((a,b),(a',b')):=(a\oplus a',\,b\oplus b')$.
--
--   The **utility** is $U_x(a,b):=\mathbf 1\{a=x\}$: the only candidate with positive utility that a policy can ever produce is $(x,x\cdot x)$.
--
--   These are the objects of every statement of the mission: generation and recombination are the only ways a policy can produce candidates, and $U_x$ is the success criterion.
--
--   **Formalization Note** $\{0,1\}^n$ is $\mathbb F_2^n$ = `V n` = `Fin n → ZMod 2` and $a\cdot x$ is the binary pairing `dot`, both from the published definition `ExtremalForrelation_Nonadaptive_Basic`. XOR is the addition of the product module `V n × ZMod 2`. `genLaw x` is the law of $\mathrm{Gen}_x()$ as a probability mass function, and `hit x z` is the Boolean $U_x(z)=1$.
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), §6 'Parity learning', p.8

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Basic

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Candidates of the parity-learning instance `𝔊^par_x`** (Brandenberger, Doron-Arad, Mossel,
*Genetic Algorithms with Optimization Guided Operators*, STOC 2027 submission, manuscript sha256
f89f4f77…, §6 "Parity learning", p.8): the candidate space is `X := {0,1}ⁿ × {0,1}`; a candidate
`(a, b)` is read as the linear equation `a · x = b` about the hidden `x`.

**Formalization Note.** `{0,1}ⁿ` is `𝔽₂ⁿ = V n = Fin n → ZMod 2` from the published definition
`ExtremalForrelation_Nonadaptive_Basic`, and `{0,1}` is `ZMod 2`. The recombination operator
`XOR((a, b), (a', b')) := (a ⊕ a', b ⊕ b')` is the addition `+` of the product module
`V n × ZMod 2` (coordinatewise addition modulo 2). -/
abbrev Cand (n : ℕ) : Type := V n × ZMod 2

/-- **The generation operator `Gen_x`** (§6, p.8): `Gen_x()` returns `(a, b)`, where
`a ∼ Unif({0,1}ⁿ)` and `b = a · x mod 2`. This is its law, a probability mass function on candidates.

**Formalization Note.** `a · x mod 2` is the published binary pairing `dot a x ∈ ZMod 2`. -/
noncomputable def genLaw {n : ℕ} (x : V n) : PMF (Cand n) :=
  (PMF.uniformOfFintype (V n)).map (fun a => (a, dot a x))

/-- **The utility `U_x`** (§6, p.8): `U_x(a, b) := 1{a = x}`; `hit x z = true` exactly when
`U_x(z) = 1`. Only the first coordinate is compared, as on the page. -/
def hit {n : ℕ} (x : V n) (z : Cand n) : Bool := decide (z.1 = x)

end GMRDiversity


