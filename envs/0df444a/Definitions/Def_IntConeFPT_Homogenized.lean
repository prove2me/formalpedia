-- Prove2me | Definitions.Def_IntConeFPT_Homogenized
-- name    : IntConeFPT_Homogenized
-- status  : Definition
-- author  : @ohnesorgefelix
-- created : 2026-11-24T11:08:04.838005+00:00
-- url     : https://prove2.me/theorems/843cc06c-f47f-4471-a254-abf9c9b40ca6
-- title:
--   Denominator-cleared integral description, homogenized instance $\hat I$, rational certificate cost, and output resolution (§3.6)
-- statement:
--   Let $I$ be an instance of the integer cone optimization problem (♣) with dimensions $d, k, \tau \ge 0$, local systems $A^{(t)} x + B^{(t)} u \le b^{(t)}$ defining $P^{(t)} \subseteq \mathbb{R}^{d+k}$, dense rational cost polynomials $f^{(t)}$, aggregate system $Q_Y y + Q_V v \le c_Q$ defining $Q \subseteq \mathbb{R}^{d+k}$, and typewise aggregate system $\sum_{t=1}^{\tau} (A_Y^{(t)} y^{(t)} + A_V^{(t)} v^{(t)} + A_{N,\cdot,t} N^{(t)}) \le c_A$ defining $\mathcal{A} \subseteq \mathbb{R}^{\tau(d+k+1)}$.
--
--   Following Section 3.6 (pp. 17–18) of Jansen–Ohnesorge–Schumacher, this module establishes five auxiliary constructions used to remove the multiplicity bound and detect unboundedness in the proof of Theorem 1:
--
--   1. **Rowwise denominator clearing** (`clearIntDesc`): combining the rows of $Q$ and $\mathcal{A}$ into a single system $W y_{\mathrm{agg}} \le c_{\mathrm{agg}}$ on $y_{\mathrm{agg}} = ((y^{(t)}, v^{(t)}, N^{(t)}))_{t=1}^{\tau}$ and multiplying each row of $Q$, $\mathcal{A}$, and $P^{(t)}$ by the product of the denominators appearing in that row yields an integral description of $(Q, \mathcal{A}, (P^{(t)})_t)$.
--   2. **Coefficient bound $U$** (`coeffBoundU`): given a coordinate box bound $M \in \mathbb{N}$,
--   $$
--   U(I, M) := (M + 1)\Bigl(1 + \|W\|_1 + \|c_{\mathrm{agg}}\|_1 + \sum_{t=1}^{\tau}\bigl(\|A^{(t)}_{\mathrm{int}}\|_1 + \|B^{(t)}_{\mathrm{int}}\|_1 + \|b^{(t)}_{\mathrm{int}}\|_1\bigr)\Bigr) \ge 1
--   $$
--   bounds all cleared integer entries and all coefficients obtained by substituting an integer vector $x \in [-M, M]^d$ into a local or aggregate row.
--   3. **Homogenized instance $\widehat{I}$** (`homInstance`): replacing the right-hand sides $c_Q$ and $c_A$ of $Q$ and $\mathcal{A}$ by $0$ while retaining the same local polytopes $P^{(t)}$ and cost polynomials $f^{(t)}$, so that its aggregate polyhedra are $\widehat{Q}$ and $\widehat{\mathcal{A}}$.
--   4. **Rational certificate cost** (`ratEvalF`, `ratCertCost`): exact evaluation in $\mathbb{Q}$ of $\sum_{t=1}^{\tau} \sum_{(x,u,\mu)} \mu\, f^{(t)}(x)$ on any rational generator certificate.
--   5. **Output resolution** (`resolveOutput`): combining the bounded-multiplicity outputs $o_0$ on $(I, N_\star)$ and $\widehat{o}$ on $(\widehat{I}, N_\star)$ by reporting *infeasible* when $o_0$ is infeasible, reporting *unbounded* when $o_0$ is optimal and $\widehat{o}$ has negative cost, and returning $o_0$ otherwise.
--
--   These constructions isolate the exact algebraic and combinatorial objects shared between the structural reduction of Theorem 1 and its Turing-machine orchestration.
--
--   **Formalization Note** The combined row index of $W y_{\mathrm{agg}} \le c_{\mathrm{agg}}$ has type `Fin (I.mQ + I.mA)` via `Fin.addCases`, and `homInstance I` preserves the fields `d`, `k`, `τ`, `P`, `Px`, and `f` definitionally.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), §3.6, pp.17–18, eq. (3.4) and Proof of Theorem 1

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation

namespace IntConeFPT

open OnlineCRS.Combine

/-- Clear the denominator of `r : ℚ` using a multiple `q : ℕ` of `r.den` (§3.6, p.17). -/
def clearRat (q : ℕ) (r : ℚ) : ℤ :=
  r.num * (q / r.den : ℕ)

/-- Product of the denominators in row `i` of `Q` (§3.6, p.17). -/
def rowDenomQ (I : Instance) (i : Fin I.mQ) : ℕ :=
  (∏ j : Fin I.d, (I.QY i j).den) * (∏ j : Fin I.k, (I.QV i j).den) * (I.cQ i).den

/-- Product of the denominators in row `i` of `A` (§3.6, p.17). -/
def rowDenomA (I : Instance) (i : Fin I.mA) : ℕ :=
  (∏ t : Fin I.τ, ((∏ j : Fin I.d, (I.AY t i j).den) * (∏ j : Fin I.k, (I.AV t i j).den) *
    (I.AN i t).den)) * (I.cA i).den

/-- Product of the denominators in row `i` of the local system of `P^(t)` (§3.6, p.17). -/
def rowDenomLoc (I : Instance) (t : Fin I.τ) (i : Fin (I.m t)) : ℕ :=
  (∏ j : Fin I.d, (I.Aloc t i j).den) * (∏ j : Fin I.k, (I.Bloc t i j).den) * (I.bloc t i).den

/-- **Canonical integral description of an instance** (§3.6, p.17): combine the rows of `Q` and `A`
into `W y_agg ≤ c_agg` and clear denominators row by row in `Q`, `A`, and each `P^(t)`. -/
def clearIntDesc (I : Instance) : IntDesc I where
  mW := I.mQ + I.mA
  WY t := Matrix.of (Fin.addCases
    (fun i j => clearRat (rowDenomQ I i) (I.QY i j))
    (fun i j => clearRat (rowDenomA I i) (I.AY t i j)))
  WV t := Matrix.of (Fin.addCases
    (fun i j => clearRat (rowDenomQ I i) (I.QV i j))
    (fun i j => clearRat (rowDenomA I i) (I.AV t i j)))
  WN := Matrix.of (Fin.addCases
    (fun _ _ => 0)
    (fun i t => clearRat (rowDenomA I i) (I.AN i t)))
  cW := Fin.addCases
    (fun i => clearRat (rowDenomQ I i) (I.cQ i))
    (fun i => clearRat (rowDenomA I i) (I.cA i))
  mL := I.m
  LA t := Matrix.of fun i j => clearRat (rowDenomLoc I t i) (I.Aloc t i j)
  LB t := Matrix.of fun i j => clearRat (rowDenomLoc I t i) (I.Bloc t i j)
  Lb t i := clearRat (rowDenomLoc I t i) (I.bloc t i)

/-- **Computable integer bound `U ≥ 1`** (§3.6, p.17) bounding all cleared coefficients and
right-hand sides of `clearIntDesc I` as well as the coefficients obtained by substituting any
integer-coordinate vector `x ∈ [−M, M]^d` into a local or aggregate constraint. -/
def coeffBoundU (I : Instance) (M : ℕ) : ℕ :=
  let D := clearIntDesc I
  (M + 1) * (1 +
    (∑ t, ∑ i, ∑ j, (D.WY t i j).natAbs) +
    (∑ t, ∑ i, ∑ j, (D.WV t i j).natAbs) +
    (∑ i, ∑ t, (D.WN i t).natAbs) +
    (∑ i, (D.cW i).natAbs) +
    (∑ t, ∑ i, ∑ j, (D.LA t i j).natAbs) +
    (∑ t, ∑ i, ∑ j, (D.LB t i j).natAbs) +
    (∑ t, ∑ i, (D.Lb t i).natAbs))

/-- **The homogenized instance `Î`** (§3.6, Proof of Theorem 1, p.18): replace the right-hand sides
in the descriptions of `Q` and `A` by zero, obtaining polyhedra `Q̂` and `Â`, with the same
generator domains and cost polynomials. -/
def homInstance (I : Instance) : Instance :=
  { I with
    cQ := fun _ => 0
    cA := fun _ => 0 }

/-- Exact rational evaluation of the cost polynomial `f^(t)` at an integer vector `x ∈ Z^d`. -/
def ratEvalF (I : Instance) (t : Fin I.τ) (x : Fin I.d → ℤ) : ℚ :=
  ∑ j : Fin (monomials I.d (I.deg t)).length,
    I.coeff t j * ∏ i, (x i : ℚ) ^ ((monomials I.d (I.deg t)).get j i)

/-- Exact rational cost `Σ_t Σ_{(x,u,μ)∈cert(t)} μ f^(t)(x)` of a certificate `cert`. -/
def ratCertCost (I : Instance) (cert : Cert I) : ℚ :=
  ∑ t : Fin I.τ, ((cert t).map fun c => (c.2.2 : ℚ) * ratEvalF I t c.1).sum

/-- **Output combination rule of Theorem 1** (§3.6, Proof of Theorem 1, p.18): given the output `o₀`
of Proposition 14 on `(I, N⋆)` and `oHom` on `(homInstance I, N⋆)`, report `infeasible` if `o₀` is
`infeasible`, report `unbounded` if `o₀` is `optimal` and `oHom` has negative cost, and otherwise
return `o₀`. -/
def resolveOutput (I : Instance) (o₀ : Output I) (oHom : Output (homInstance I)) : Output I :=
  match o₀ with
  | .infeasible => .infeasible
  | .unbounded => .infeasible
  | .optimal y₀ v₀ cert₀ =>
    match oHom with
    | .optimal _ _ certHom =>
      if ratCertCost I certHom < 0 then .unbounded else .optimal y₀ v₀ cert₀
    | _ => .optimal y₀ v₀ cert₀

end IntConeFPT


