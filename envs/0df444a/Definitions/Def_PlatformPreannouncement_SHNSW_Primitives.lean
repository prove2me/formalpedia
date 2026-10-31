-- Prove2me | Definitions.Def_PlatformPreannouncement_SHNSW_Primitives
-- name    : PlatformPreannouncement_SHNSW_Primitives
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:17:37.127647+00:00
-- url     : https://prove2.me/theorems/87b318bb-1f45-4208-b2d8-91e1645a01cb
-- title:
--   SH-NSW announcements, loyal markets, expected utilities and profits
-- statement:
--   Two identical firms $i\in\{0,1\}$ occupy the endpoints of a unit Hotelling line. The users and developers are separate uniform unit new markets. Each side also has a loyal installed unit market, split equally between firms, so $m_u^i=m_d^i=1/2$. Old agents adopt the new version without switching. Each new agent chooses one firm.
--
--   The raw parameter record consists of real numbers $t,\alpha,\beta,\theta,c,k,\mu,\delta$. Their economic domain is stated in the theorem. A firm chooses formal, informal, or no announcement, denoted $F,I,N$. Its user-information multiplier, developer-information multiplier, and prelaunch cost are respectively $(1,1,c)$, $(\mu,\delta,kc)$, and $(0,0,0)$. An announcement history is an ordered pair of modes; a tariff is a pair of real user price and developer fee. Tariff nonnegativity is imposed by market feasibility.
--
--   Allocation records contain the two real left-firm cutoffs $q_u,q_d$, with new demands $n_u^0=q_u,n_u^1=1-q_u$ and $n_d^0=q_d,n_d^1=1-q_d$. Bounds are imposed by the market relation. If firm $i$ has information multipliers $a_i,b_i$, then before transport its user and developer values are
--   $$V_u^i=\theta+\alpha(1/2+a_i n_u^i)+\beta(1/2+a_i n_d^i)-p_i,
--   \qquad V_d^i=\theta+\beta(1/2+b_i n_u^i)-l_i.$$
--   Actual location utility subtracts $tx$ at firm 0 and $t(1-x)$ at firm 1. There is no same-side developer externality. The announcement multipliers remain fixed during pricing and adoption, including at asymmetric histories. Net firm profit is
--   $$\Pi_i=p_i(1/2+n_u^i)+l_i(1/2+n_d^i)-C_i.$$
--   This definition supplies only primitives; it asserts no allocation or pricing optimality, and imposes no functional relationship between information and the informal cost multiplier.
-- source:
--   Chellappa and Mukherjee (2020), DOI 10.1287/mnsc.2020.3606, held source.pdf §§2–2.4, pp. 10–22, equations (1)–(11), Figure 1 p. 16; identical installed bases p. 24.

import Mathlib.Data.Real.Basic

namespace PlatformPreannouncement.SHNSW

inductive Mode where
  | formal | informal | none
  deriving DecidableEq

abbrev Firm := Fin 2
abbrev History := Mode × Mode
abbrev Tariff := ℝ × ℝ
abbrev Prices := Firm → Tariff

/-- Raw economic parameters; the theorem states all domain conditions. -/
structure Parameters where
  t : ℝ
  alpha : ℝ
  beta : ℝ
  theta : ℝ
  c : ℝ
  k : ℝ
  mu : ℝ
  delta : ℝ

def modeAt (h : History) (i : Firm) : Mode := if i = 0 then h.1 else h.2

def userInformation (P : Parameters) : Mode → ℝ
  | .formal => 1
  | .informal => P.mu
  | .none => 0

def developerInformation (P : Parameters) : Mode → ℝ
  | .formal => 1
  | .informal => P.delta
  | .none => 0

def announcementCost (P : Parameters) : Mode → ℝ
  | .formal => P.c
  | .informal => P.k * P.c
  | .none => 0

/-- Each side's loyal installed market has mass one, equally split. -/
noncomputable def installedBase (_i : Firm) : ℝ := 1 / 2

/-- Cutoffs for the two separate new unit uniform markets. -/
structure Allocation where
  users : ℝ
  developers : ℝ

def newUsers (q : Allocation) (i : Firm) : ℝ :=
  if i = 0 then q.users else 1 - q.users

def newDevelopers (q : Allocation) (i : Firm) : ℝ :=
  if i = 0 then q.developers else 1 - q.developers

noncomputable def userValue (P : Parameters) (h : History) (r : Prices)
    (q : Allocation) (i : Firm) : ℝ :=
  P.theta + P.alpha * (installedBase i + userInformation P (modeAt h i) * newUsers q i) +
    P.beta * (installedBase i + userInformation P (modeAt h i) * newDevelopers q i) -
    (r i).1

noncomputable def developerValue (P : Parameters) (h : History) (r : Prices)
    (q : Allocation) (i : Firm) : ℝ :=
  P.theta + P.beta * (installedBase i + developerInformation P (modeAt h i) * newUsers q i) -
    (r i).2

def distance (i : Firm) (x : ℝ) : ℝ := if i = 0 then x else 1 - x

noncomputable def userUtility (P : Parameters) (h : History) (r : Prices)
    (q : Allocation) (i : Firm) (x : ℝ) : ℝ :=
  userValue P h r q i - P.t * distance i x

noncomputable def developerUtility (P : Parameters) (h : History) (r : Prices)
    (q : Allocation) (i : Firm) (x : ℝ) : ℝ :=
  developerValue P h r q i - P.t * distance i x

noncomputable def profit (P : Parameters) (h : History) (r : Prices)
    (q : Allocation) (i : Firm) : ℝ :=
  (r i).1 * (installedBase i + newUsers q i) +
    (r i).2 * (installedBase i + newDevelopers q i) - announcementCost P (modeAt h i)

end PlatformPreannouncement.SHNSW


