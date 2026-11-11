-- Prove2me | Definitions.Def_AnyWE_CEFCorrectness_Primitives
-- name    : AnyWE_CEFCorrectness_Primitives
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:51:07.302728+00:00
-- url     : https://prove2.me/theorems/2e70acb7-0a6a-4f88-9df1-fb859a3e76a7
-- title:
--   NP relations, commitments in the CRS model, length-doubling PRGs, NIWI proofs and witness encryption, with polynomial security against non-uniform circuits (Definitions 4.3, 4.14, 4.16)
-- statement:
--   All objects are families indexed by the security parameter $\lambda$, at the lengths at which they are used. A function $\nu$ is **negligible** if for every $c>0$, $|\nu(\lambda)|<\lambda^{-c}$ for all large $\lambda$ (the referenced definition). An experiment is **polynomially secure** if for every polynomial $s$ there is a negligible $\epsilon$ such that, for all sufficiently large $\lambda$, every circuit of size at most $s(\lambda)$ has advantage at most $\epsilon(\lambda)$ (§4.2). A circuit family is **efficient** if its encoding length (inputs, outputs, gates) is at most a polynomial in $\lambda$.
--
--   **Relations.** An NP relation at fixed lengths has instances in $\{0,1\}^{n(\lambda)}$, witnesses in $\{0,1\}^{m(\lambda)}$ and a predicate $R_\lambda(x,w)$; the relation of circuits $C_\lambda$ is $R_\lambda(x,w)\iff C_\lambda(x,w)=1$. A relation family additionally reads a description string $d$ (a relation handed to a setup algorithm), $R_\lambda[d](X,w)$.
--
--   **Commitments (Definition 4.3).** Polynomial lengths $\ell_{crs},\ell_{rand},\ell_{com}$; $\mathrm{Com.Gen}(1^\lambda)$ outputs a uniformly random $\mathrm{crs}\in\{0,1\}^{\ell_{crs}}$; $\mathrm{Com}(\mathrm{crs},b;r)\in\{0,1\}^{\ell_{com}}$ is an efficient circuit. It is *computationally hiding*: the advantage $|\Pr[D(\mathrm{crs},\mathrm{Com}(\mathrm{crs},0;r))=1]-\Pr[D(\mathrm{crs},\mathrm{Com}(\mathrm{crs},1;r))=1]|$ over independent uniform $\mathrm{crs},r$ is polynomially secure; and *statistically binding*: for a negligible $\nu$ and every $\lambda$,
--   $$\Pr_{\mathrm{crs}}\big[\exists r_0,r_1:\ \mathrm{Com}(\mathrm{crs},0;r_0)=\mathrm{Com}(\mathrm{crs},1;r_1)\big]\le\nu(\lambda).$$
--
--   **PRG (§4.2.3).** An efficient $G:\{0,1\}^\lambda\to\{0,1\}^{2\lambda}$ with $|\Pr[D(G(U_\lambda))=1]-\Pr[D(U_{2\lambda})=1]|$ polynomially secure.
--
--   **NIWI (Definition 4.14).** For a relation family: $\mathrm{Gen}(1^\lambda,d;\rho)\to\mathrm{crs}$, $P(\mathrm{crs},X,w;r)\to\pi$, $V(\mathrm{crs},X,\pi)\in\{0,1\}$, all efficient. *Completeness*: a negligible $\nu$ with $\Pr[V(\mathrm{crs},X,P(\mathrm{crs},X,w))=1]\ge1-\nu(\lambda)$ for every $\lambda$ with instance and witness lengths at most $2^\lambda$, every $d$ and every valid $(X,w)$. *Statistical soundness*: a negligible $\nu$ with $\Pr_\rho[\exists X\notin L_d,\ \pi:\ V(\mathrm{crs},X,\pi)=1]\le\nu(\lambda)$ for every $\lambda$ and $d$. *Witness indistinguishability*: for $(d,X,w_0,w_1)$ with both witnesses valid, fixed before setup, the advantage of distinguishing $(\mathrm{crs},P(\mathrm{crs},X,w_0))$ from $(\mathrm{crs},P(\mathrm{crs},X,w_1))$ is polynomially secure.
--
--   **Witness encryption (Definition 4.16).** $\mathrm{Enc}(1^\lambda,X,b;r_1)\to\mathrm{ct}$ and a probabilistic $\mathrm{Dec}(\mathrm{ct},X,w;r_2)\in\{0,1,\bot\}$, both efficient. *Statistical correctness*: a negligible $\nu$ with
--   $$\Pr_{r_1,r_2}\big[\mathrm{Dec}(\mathrm{Enc}(1^\lambda,X,b;r_1),X,w;r_2)=b\big]\ge1-\nu(\lambda)$$
--   for every $\lambda$ with lengths at most $2^\lambda$, every valid $(X,w)$ and every $b$. *Semantic security*: for every false instance $X_\lambda$ (hardwirable into the adversary), the advantage of distinguishing $\mathrm{Enc}(X_\lambda,0)$ from $\mathrm{Enc}(X_\lambda,1)$ is polynomially secure.
--
--   These are the ingredients of the transformation $\mathrm{WE}'$; correctness is only statistical, and decryption may be randomized and may output $\bot$.
--
--   **Formalization Note.** Algorithms are circuit families at the lengths where they are used (instance and witness lengths are functions of $\lambda$, so "poly$(\lambda,n,m)$" is poly$(\lambda)$). An output in $\{0,1,\bot\}$ is two bits $(\mathit{valid},\mathit{bit})$: the bit if $\mathit{valid}=1$, $\bot$ if $\mathit{valid}=0$. Com.Gen's uniformly random reference string is its own random tape. For a relation family the NIWI's negligible errors and its witness indistinguishability are uniform over the description $d$.
-- source:
--   Jain, Jin, Mathialagan, SNARGs from any Witness Encryption, and More, STOC 2027 submission (manuscript sha256 9bc2f227…), p. 22 (security conventions, relations); p. 23, Definition 4.3; p. 25, §4.2.3; pp. 28-30, Definitions 4.13-4.14; pp. 30-31, Definition 4.16

import Mathlib
import Definitions.Def_QuantumPRC_Negligible
import Definitions.Def_AnyWE_CEFCorrectness_Circuit
set_option autoImplicit false

/-!
# Relations, commitments, PRGs, NIWI proofs and witness encryption, as circuit families

Jain, Jin, Mathialagan, *SNARGs from any Witness Encryption, and More*, STOC 2027 submission
(manuscript sha256 9bc2f227…), §4.2 p. 22 (security conventions, relations, Remark 4.2),
Definition 4.3 p. 23 (commitments), §4.2.3 p. 25 (length-doubling PRG), Definitions 4.13–4.14
pp. 28–30 (NIWI), Definition 4.16 pp. 30–31 (witness encryption).

Every algorithm is a family of circuits indexed by the security parameter `λ`, at the instance and
witness lengths at which it is used; its random tape is an input block. Adversaries are
non-uniform circuits (advice = constant gates), of size at most `s(λ)`. Polynomial security:
for every polynomial `s` there is a negligible `ϵ` such that, for all sufficiently large `λ`, every
adversary of size at most `s(λ)` has advantage at most `ϵ(λ)`.
-/

namespace AnyWE.CEFCorrectness

open QuantumPRC

/-- An NP relation at fixed lengths: instances of length `instLen λ`, witnesses of length
`witLen λ`. -/
structure NPRel where
  instLen : ℕ → ℕ
  witLen : ℕ → ℕ
  holds : ∀ lam, Bits (instLen lam) → Bits (witLen lam) → Prop

/-- A family of NP relations indexed by a description string of length `descLen λ` (the relation
given to `Gen` as input, e.g. a relation that hardwires a sampled reference string). -/
structure NPRelFam where
  descLen : ℕ → ℕ
  instLen : ℕ → ℕ
  witLen : ℕ → ℕ
  holds : ∀ lam, Bits (descLen lam) → Bits (instLen lam) → Bits (witLen lam) → Prop

/-- A circuit family has polynomial encoding length (inputs, outputs and gates): the circuit form
of "polynomial running time" (Remark 4.2). -/
def PolyFamily {a b : ℕ → ℕ} (C : ∀ lam, Circuit (a lam) (b lam)) : Prop :=
  ∃ p : Polynomial ℕ, ∀ lam, (C lam).encLen ≤ p.eval lam

/-- **Polynomial security** of an experiment whose distinguishers read `L λ` bits and whose
advantage against `D` is `adv λ D`. -/
def PolySecure (L : ℕ → ℕ) (adv : ∀ lam, Circuit (L lam) 1 → ℝ) : Prop :=
  ∀ s : Polynomial ℕ, ∃ ϵ : ℕ → ℝ, Negligible ϵ ∧
    ∀ᶠ lam in Filter.atTop, ∀ D : Circuit (L lam) 1, D.size ≤ s.eval lam → adv lam D ≤ ϵ lam

/-! ### Commitments in the CRS model (Definition 4.3) -/

/-- A non-interactive bit commitment in the CRS model: `Com.Gen(1^λ)` outputs a uniformly random
`crs_Com ∈ {0,1}^{ℓ_crs(λ)}` (its random tape), and `Com(crs_Com, b; r)` with
`r ∈ {0,1}^{ℓ_rand(λ)}` is the circuit `com λ`. -/
structure Commitment where
  crsLen : ℕ → ℕ
  randLen : ℕ → ℕ
  comLen : ℕ → ℕ
  com : ∀ lam, Circuit (crsLen lam + 1 + randLen lam) (comLen lam)

namespace Commitment

/-- `Com(crs, b; r)`. -/
def commit (C : Commitment) (lam : ℕ) (crs : Bits (C.crsLen lam)) (b : Bool)
    (r : Bits (C.randLen lam)) : Bits (C.comLen lam) :=
  (C.com lam).eval (Fin.append (Fin.append crs (fun _ => b)) r)

/-- Definition 4.3 with polynomial hiding: polynomial lengths and running time, computational
hiding (against non-uniform distinguishers of every polynomial size, over independent uniform
`crs_Com, r`), and statistical binding (a negligible bound, for every `λ`, on the probability over
`crs_Com` that some commitment opens to both bits). -/
def IsCommitment (C : Commitment) : Prop :=
  IsPoly C.crsLen ∧ IsPoly C.randLen ∧ IsPoly C.comLen ∧ PolyFamily C.com ∧
  PolySecure (fun lam => C.crsLen lam + C.comLen lam) (fun lam D =>
    |prob (C.crsLen lam + C.randLen lam)
        (fun v => D.eval (Fin.append v.left (C.commit lam v.left false v.right)) 0 = true) -
      prob (C.crsLen lam + C.randLen lam)
        (fun v => D.eval (Fin.append v.left (C.commit lam v.left true v.right)) 0 = true)|) ∧
  ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
    prob (C.crsLen lam) (fun crs => ∃ r₀ r₁ : Bits (C.randLen lam),
      C.commit lam crs false r₀ = C.commit lam crs true r₁) ≤ ν lam

end Commitment

/-! ### Length-doubling PRG (§4.2.3) -/

/-- A length-doubling function `G : {0,1}^λ → {0,1}^{2λ}`, as a circuit family. -/
structure PRG where
  G : ∀ lam, Circuit lam (2 * lam)

/-- A polynomially secure length-doubling PRG: deterministic polynomial time, and
`|Pr[D(G(U_λ)) = 1] - Pr[D(U_{2λ}) = 1]|` is negligible for every polynomial-size `D`. -/
def PRG.IsSecure (P : PRG) : Prop :=
  PolyFamily P.G ∧
  PolySecure (fun lam => 2 * lam) (fun lam D =>
    |prob lam (fun u => D.eval ((P.G lam).eval u) 0 = true) -
      prob (2 * lam) (fun v => D.eval v 0 = true)|)

/-! ### NIWI proofs (Definition 4.14, with the syntax and properties of Definition 4.13) -/

/-- A non-interactive proof system for a relation family: `Gen(1^λ, desc; ρ)`, `P(crs, X, w; r)`,
`V(crs, X, π)`. -/
structure NIWIScheme (R : NPRelFam) where
  crsLen : ℕ → ℕ
  genTape : ℕ → ℕ
  proofLen : ℕ → ℕ
  proveTape : ℕ → ℕ
  gen : ∀ lam, Circuit (R.descLen lam + genTape lam) (crsLen lam)
  prove : ∀ lam, Circuit (crsLen lam + R.instLen lam + R.witLen lam + proveTape lam) (proofLen lam)
  verify : ∀ lam, Circuit (crsLen lam + R.instLen lam + proofLen lam) 1

namespace NIWIScheme

variable {R : NPRelFam}

/-- `crs ← Gen(1^λ, desc; ρ)`. -/
def crs (S : NIWIScheme R) (lam : ℕ) (d : Bits (R.descLen lam)) (ρ : Bits (S.genTape lam)) :
    Bits (S.crsLen lam) :=
  (S.gen lam).eval (Fin.append d ρ)

/-- `π ← P(crs, X, w; r)`. -/
def proof (S : NIWIScheme R) (lam : ℕ) (crs : Bits (S.crsLen lam)) (X : Bits (R.instLen lam))
    (w : Bits (R.witLen lam)) (r : Bits (S.proveTape lam)) : Bits (S.proofLen lam) :=
  (S.prove lam).eval (Fin.append (Fin.append (Fin.append crs X) w) r)

/-- `V(crs, X, π)`. -/
def accepts (S : NIWIScheme R) (lam : ℕ) (crs : Bits (S.crsLen lam)) (X : Bits (R.instLen lam))
    (pf : Bits (S.proofLen lam)) : Bool :=
  (S.verify lam).eval (Fin.append (Fin.append crs X) pf) 0

/-- Definition 4.14 at the relation's lengths, polynomial witness indistinguishability:
completeness (a negligible error, for every `λ` with lengths `≤ 2^λ`, every description and every
valid pair); efficiency; statistical soundness (for every `λ` and description, the probability
over setup that some false statement has an accepting proof is negligible); and witness
indistinguishability for `(desc, X, w₀, w₁)` fixed before setup. -/
def IsNIWI (S : NIWIScheme R) : Prop :=
  (∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam, R.instLen lam ≤ 2 ^ lam → R.witLen lam ≤ 2 ^ lam →
    ∀ (d : Bits (R.descLen lam)) (X : Bits (R.instLen lam)) (w : Bits (R.witLen lam)),
      R.holds lam d X w →
      1 - ν lam ≤ prob (S.genTape lam + S.proveTape lam) (fun v =>
        S.accepts lam (S.crs lam d v.left) X (S.proof lam (S.crs lam d v.left) X w v.right) = true)) ∧
  PolyFamily S.gen ∧ PolyFamily S.prove ∧ PolyFamily S.verify ∧
  (∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam (d : Bits (R.descLen lam)),
    prob (S.genTape lam) (fun ρ => ∃ X : Bits (R.instLen lam),
      (∀ w, ¬ R.holds lam d X w) ∧ ∃ pf, S.accepts lam (S.crs lam d ρ) X pf = true) ≤ ν lam) ∧
  ∀ s : Polynomial ℕ, ∃ ϵ : ℕ → ℝ, Negligible ϵ ∧ ∀ᶠ lam in Filter.atTop,
    ∀ (d : Bits (R.descLen lam)) (X : Bits (R.instLen lam)) (w₀ w₁ : Bits (R.witLen lam)),
      R.holds lam d X w₀ → R.holds lam d X w₁ →
      ∀ D : Circuit (S.crsLen lam + S.proofLen lam) 1, D.size ≤ s.eval lam →
        |prob (S.genTape lam + S.proveTape lam) (fun v =>
            D.eval (Fin.append (S.crs lam d v.left)
              (S.proof lam (S.crs lam d v.left) X w₀ v.right)) 0 = true) -
          prob (S.genTape lam + S.proveTape lam) (fun v =>
            D.eval (Fin.append (S.crs lam d v.left)
              (S.proof lam (S.crs lam d v.left) X w₁ v.right)) 0 = true)| ≤ ϵ lam

end NIWIScheme

/-! ### Witness encryption (Definition 4.16) -/

/-- The output of a decryption circuit, two bits `(valid, bit)`: the bit `bit` if `valid = 1`, and
`⊥` if `valid = 0`. -/
def decOut (o : Bits 2) : Option Bool := if o 0 then some (o 1) else none

/-- A witness encryption scheme for `R`, with probabilistic decryption: `Enc(1^λ, X, b; r₁)` and
`Dec(ct, X, w; r₂) ∈ {0, 1, ⊥}` (encoded by `decOut`). -/
structure WEScheme (R : NPRel) where
  ctLen : ℕ → ℕ
  encTape : ℕ → ℕ
  decTape : ℕ → ℕ
  enc : ∀ lam, Circuit (R.instLen lam + 1 + encTape lam) (ctLen lam)
  dec : ∀ lam, Circuit (ctLen lam + R.instLen lam + R.witLen lam + decTape lam) 2

namespace WEScheme

variable {R : NPRel}

/-- `ct ← Enc(1^λ, X, b; r₁)`. -/
def encrypt (W : WEScheme R) (lam : ℕ) (X : Bits (R.instLen lam)) (b : Bool)
    (r : Bits (W.encTape lam)) : Bits (W.ctLen lam) :=
  (W.enc lam).eval (Fin.append (Fin.append X (fun _ => b)) r)

/-- `Dec(ct, X, w; r₂)`. -/
def decrypt (W : WEScheme R) (lam : ℕ) (ct : Bits (W.ctLen lam)) (X : Bits (R.instLen lam))
    (w : Bits (R.witLen lam)) (r : Bits (W.decTape lam)) : Option Bool :=
  decOut ((W.dec lam).eval (Fin.append (Fin.append (Fin.append ct X) w) r))

/-- Definition 4.16 with statistical correctness and polynomial semantic security: correctness
(a negligible error, for every `λ` with lengths `≤ 2^λ`, every valid pair and every bit, over
independent `r₁, r₂`); efficiency; and semantic security for every false instance `X_λ` (which
may be hardwired into the adversary). -/
def IsWE (W : WEScheme R) : Prop :=
  (∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam, R.instLen lam ≤ 2 ^ lam → R.witLen lam ≤ 2 ^ lam →
    ∀ (X : Bits (R.instLen lam)) (w : Bits (R.witLen lam)), R.holds lam X w → ∀ b : Bool,
      1 - ν lam ≤ prob (W.encTape lam + W.decTape lam) (fun v =>
        W.decrypt lam (W.encrypt lam X b v.left) X w v.right = some b)) ∧
  PolyFamily W.enc ∧ PolyFamily W.dec ∧
  ∀ s : Polynomial ℕ, ∃ ϵ : ℕ → ℝ, Negligible ϵ ∧ ∀ᶠ lam in Filter.atTop,
    ∀ X : Bits (R.instLen lam), (∀ w, ¬ R.holds lam X w) →
      ∀ D : Circuit (W.ctLen lam) 1, D.size ≤ s.eval lam →
        |prob (W.encTape lam) (fun r => D.eval (W.encrypt lam X false r) 0 = true) -
          prob (W.encTape lam) (fun r => D.eval (W.encrypt lam X true r) 0 = true)| ≤ ϵ lam

end WEScheme

/-- The relation `R(x, w) = C_λ(x, w)` of a family of relation circuits with instance length `n`
and witness length `m` (Remark 4.2: `R` unrolled at these lengths). -/
def relOf (n m : ℕ → ℕ) (RC : ∀ lam, Circuit (n lam + m lam) 1) : NPRel where
  instLen := n
  witLen := m
  holds := fun lam x w => (RC lam).eval (Fin.append x w) 0 = true

end AnyWE.CEFCorrectness


