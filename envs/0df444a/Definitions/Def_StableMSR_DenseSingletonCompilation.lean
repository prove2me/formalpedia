-- Prove2me | Definitions.Def_StableMSR_DenseSingletonCompilation
-- name    : StableMSR_DenseSingletonCompilation
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-23T00:12:06.05804+00:00
-- url     : https://prove2.me/theorems/f4279f36-4d14-4348-8027-58ed0ccef319
-- title:
--   Dense source contract for native singleton separator circuits
-- statement:
--   Dense source gates are analyzed by their ordered language. The native record emitter handles the physical realization of this language in the mission board.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution specializes the mission’s tight-block recurrence to singleton progress for the native separator construction.

import Definitions.Def_StableMSR_SingleCircuitRAM
import Definitions.Def_StableMSR_SingleWindowGrammar
open scoped Classical
set_option autoImplicit false
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.WindowCSP StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowPorts
open StableMSR.Recovery.SingleWindows StableMSR.Recovery.SingleCircuit
open StableMSR.Recovery.WindowProfiles (piece keys)
namespace StableMSR.Recovery.SingleRAM
/-- Circuit-level regional contract. The compiler's leaf now deals only in ordinary gates and one dense bitmap per gate. -/
def RegionalLanguage (x : World) (e : ℚ) (g : Gates) (roots : ℕ→ℕ) :=
  0< g.size ∧ gateAt g 0=.atom [] ∧ ∀u< x.rows,∀i< x.n,
    let r:=u*x.n+i;let p:=roots r;let lang:=Language x.n g p
    r<3*g.size ∧ p<3*g.size ∧
    (i∉keys x u → ∀L,lang L ↔ L=[]) ∧
    (i∈keys x u → scale x u≤0 → ∀L,¬lang L) ∧
    (i∈keys x u → 0< scale x u →
      let gen:=generates x (piece x u i) (scale x u) (budget (e:ℝ)) (widthBound (e:ℝ))
      (∀L,lang L → L.Nodup ∧ gen L.toFinset) ∧ ∀Q,gen Q → ∃L,lang L ∧ L.toFinset=Q)
def denseSpec (e : ℚ) (c D b : ℕ) (cmd : Cmd) :=
  ∀(x : World) (s : Store),1≤ x.k → x.k< x.n → IsMetricArray x.dist → Ready x s →
    ∃t z H,Executes x.dist cmd s t z ∧ z≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      H≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧ let y:=worldOf x.k H x.dist t
      Ready y t ∧ y.mem 1=(x.rows:ℤ) ∧ ∃g roots,1+5*(1+3*g.size*x.n*x.n)< H ∧ Input y g roots ∧ RegionalLanguage x e g roots
end StableMSR.Recovery.SingleRAM


