-- Prove2me | Definitions.Def_BianchiIX_EraReturnData
-- name    : BianchiIX_EraReturnData
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-06T00:26:14.229203+00:00
-- url     : https://prove2.me/theorems/30f082ab-b892-4bd3-b672-832c02e536ce
-- title:
--   Partial-core returns, complete era maps and successor curves
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   For $x=(p,s,a,b,c)$, put
--   $$\psi(p,z)=\frac{\sqrt3\,z}{1+p},\qquad
--   \Pi(x)=(\psi(p,s),\psi(p,a),\psi(p,b),\psi(p,c)).$$
--   For $y=(m,u,v,w)$, set $D(y)=3+m^2+K(u,v,w)$ and
--   $$\Xi_A(y)=\left(A-1,\frac{Am}{\sqrt3},\frac{Au}{\sqrt3},
--   \frac{Av}{\sqrt3},\frac{Aw}{\sqrt3}\right),\qquad
--   \Xi(y)=\Xi_{6/D(y)}(y).$$
--   Write $N(x)=(P,Q,r_1a,r_2b,r_3c)$ for the normalized vector field
--   and $\mathcal C(x)=C(p,s,a,b,c)$ for its constraint.
--
--   The normalized and projective state spaces are $\mathbb R^5$ and $\mathbb R^4$
--   with their finite-product norms. The maps $\Pi,\Xi,D,F$ act on these state spaces.
--
--   Define the core radius, angle, and clock factor by
--   $$r(m,v)=\sqrt{(m-1)^2+v^2},\qquad
--   \theta(m,v)=\operatorname{arsinh}\frac{1-m}{v},\qquad
--   d(r,u,w)=1-\frac{(u-w)^2}{r^2}.$$
--   For $y=(m,u,v,w)$, write $r_y=r(m,v)$, $\theta_y=\theta(m,v)$,
--   and $d_y=d(r_y,u,w)$. All quotients use the total convention $x/0=0$.
--
--   The core state space is $\mathbb R^3$ with coordinates $Y=(r,u,p)$.
--   Define
--   $$\eta(m,u,v,w)=(r(m,v),u,vw),\qquad
--   \iota_z(r,u,p)=\left(1-r\tanh z,u,\frac r{\cosh z},
--   \frac p{r/\cosh z}\right).$$
--   For fixed $(z,Y)$ put $v=r/\cosh z$, $w=p/v$, $d=d(r,u,w)$, and define
--   $$\mathcal V(z,Y)=\left(
--   \frac{-\kappa(u,v,w)-\tanh z\,(u-w)^2/r}{d},\quad
--   \frac{u[-r/2+\tanh z+w/\cosh z+(u^2-w^2)/(2r)]}{d},\quad
--   \frac{-2p(1+\kappa(u,v,w))}{rd}\right).$$
--
--   For real $k$, put $\varepsilon_k=1/(10000k)$ and define
--   $$\mathcal K_k=\{(m,u,v,w): |E(m,v)-k^2|\leq1/8,\quad v\geq1,
--   \quad0\leq u\leq\varepsilon_k,\quad0\leq vw\leq\varepsilon_k\}.$$
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   Write $G(y)=6F(y)/D(y)$, $\lambda(y)=6r_yd_y/D(y)$, and
--   $S_k(R,U,P)=(R,kU,P)$. Define
--   $$\mathcal P_y\xi=d\eta_y\xi-d\theta_y\xi\,\mathcal V(\theta_y,\eta(y)),
--   \qquad \mathcal W_{y,t_0,w}(t)=
--   \mathcal P_{\Psi_{t_0}(y,t)}(\mathcal J_{y,t_0}(t)w).$$
--   The entrance parametrization and radial exit factor are
--   $$e(k,u,w)=(1+\sqrt{k^2-1},u,1,w),$$
--   $$f_y=\mathcal V(\theta_y,\eta(y))_0,\qquad c_y=-\tanh\theta_y,
--   \qquad h_y=c_y+f_y/r_y,\qquad \rho_y=c_y/h_y.$$
--   For projective initial data $y$, put
--   $$A_{y,t_0}(t)=1+(\alpha_{\Xi(y),t_0}(t))_0.$$
--   Coordinates of three-vectors are indexed by $0,1,2$; projective
--   coordinates are indexed by $m,u,v,w$.
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   For $x=(p,s,a,b,c)$, put
--   $$\psi(p,z)=\frac{\sqrt3\,z}{1+p},\qquad
--   \Pi(x)=(\psi(p,s),\psi(p,a),\psi(p,b),\psi(p,c)).$$
--   For $y=(m,u,v,w)$, set $D(y)=3+m^2+K(u,v,w)$ and
--   $$\Xi_A(y)=\left(A-1,\frac{Am}{\sqrt3},\frac{Au}{\sqrt3},
--   \frac{Av}{\sqrt3},\frac{Aw}{\sqrt3}\right),\qquad
--   \Xi(y)=\Xi_{6/D(y)}(y).$$
--   Write $N(x)=(P,Q,r_1a,r_2b,r_3c)$ for the normalized vector field
--   and $\mathcal C(x)=C(p,s,a,b,c)$ for its constraint.
--
--   The normalized and projective state spaces are $\mathbb R^5$ and $\mathbb R^4$
--   with their finite-product norms. The maps $\Pi,\Xi,D,F$ act on these state spaces.
--
--   Define the core radius, angle, and clock factor by
--   $$r(m,v)=\sqrt{(m-1)^2+v^2},\qquad
--   \theta(m,v)=\operatorname{arsinh}\frac{1-m}{v},\qquad
--   d(r,u,w)=1-\frac{(u-w)^2}{r^2}.$$
--   For $y=(m,u,v,w)$, write $r_y=r(m,v)$, $\theta_y=\theta(m,v)$,
--   and $d_y=d(r_y,u,w)$. All quotients use the total convention $x/0=0$.
--
--   The core state space is $\mathbb R^3$ with coordinates $Y=(r,u,p)$.
--   Define
--   $$\eta(m,u,v,w)=(r(m,v),u,vw),\qquad
--   \iota_z(r,u,p)=\left(1-r\tanh z,u,\frac r{\cosh z},
--   \frac p{r/\cosh z}\right).$$
--   For fixed $(z,Y)$ put $v=r/\cosh z$, $w=p/v$, $d=d(r,u,w)$, and define
--   $$\mathcal V(z,Y)=\left(
--   \frac{-\kappa(u,v,w)-\tanh z\,(u-w)^2/r}{d},\quad
--   \frac{u[-r/2+\tanh z+w/\cosh z+(u^2-w^2)/(2r)]}{d},\quad
--   \frac{-2p(1+\kappa(u,v,w))}{rd}\right).$$
--
--   At $(z,Y)$ use the abbreviations
--   $$s=1/\cosh z,\quad c=-\tanh z,\quad \delta=u-w,$$
--   $$C=u(v+w-u),\quad a=-r/2+\tanh z+w/\cosh z+(u^2-w^2)/(2r),
--   \quad g=-C+c\delta^2/r.$$
--   Let $\mathcal Q(z,Y)=(C,d,a,g)$. Define the $4\times3$ matrix $H(z,Y)$
--   by its rows, in the order $(C,d,a,g)$ and columns $(r,u,p)$:
--   $$H_C=(u(s-w/r),\ v-2u+w,\ u/v),$$
--   $$H_d=(2\delta(u-2w)/r^3,\ -2\delta/r^2,\ 2\delta/(vr^2)),$$
--   $$H_a=(-1/2-sw/r+(3w^2-u^2)/(2r^2),\ u/r,\ (1-w/v)/r),$$
--   $$H_g=(-u(s-w/r)+c\delta(3w-u)/r^2,\
--   -(v-2u+w)+2c\delta/r,\ -u/v-2c\delta/(rv)).$$
--
--   Define the two rates and the $2\times3$ matrix $J$ by
--   $$L_0(z,Y)=a/d,\qquad L_1(z,Y)=-2(1+C)/(rd),$$
--   $$J_{0j}=H_{aj}/d-aH_{dj}/d^2,$$
--   $$J_{1j}=\delta_{j0}\frac{2(1+C)}{r^2d}
--   -\frac{2H_{Cj}}{rd}+\frac{2(1+C)H_{dj}}{rd^2},\qquad j=0,1,2.$$
--   Here $\delta_{j0}$ is the Kronecker symbol. The total formulas are defined
--   also when a wall amplitude vanishes, and use $x/0=0$.
--
--   Define the rates in normalized time and the positive flow factors by
--   $$R(y)=\lambda(y)L(\theta_y,\eta(y)),\qquad
--   M_i(y,t_0,a,b)=\exp\left(\int_a^b R_i(\Psi_{t_0}(y,t))\,dt\right),
--   \quad i=0,1.$$
--   The interval integral is oriented and uses its total Bochner-integral
--   definition for every choice of endpoints and initial data.
--
--   For real $k,z$, define
--   $$\Gamma_k(z)=2\arctan(\sinh z)+\frac{24}{10000k}z,
--   \qquad C_* = \exp\left(2\pi+\frac{48}{10000}\right).$$
--   Division at zero has its total real-field meaning.
--
--   Write $\mathfrak r(y)=r(y_0,y_2)$.
--   For a time function $\tau:\mathbb R^4\to\mathbb R$ put
--   $m_i^\tau(y)=M_i(y,0,0,\tau(y))$.
--   Let $\tau_\downarrow(y)$ be the infimum of positive times in the normalized
--   maximal domain at which $(\Psi_0(y,t))_v=1$ with negative event rate, and set
--   $F_\downarrow(y)=\eta(\Psi_0(y,\tau_\downarrow(y)))$.
--   The incoming condition means $y_v>1$, or $y_v=1$ and $y_m\geq1$.
--   Define
--   $$Q_k(u,p;v,dz)=|v_0|+k|v_1|+|v_2|+(k^2u+p/k)|dz|.$$
--   All vector norms are supremum norms and operator norms are induced by them.
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   For $x=(p,s,a,b,c)$, put
--   $$\psi(p,z)=\frac{\sqrt3\,z}{1+p},\qquad
--   \Pi(x)=(\psi(p,s),\psi(p,a),\psi(p,b),\psi(p,c)).$$
--   For $y=(m,u,v,w)$, set $D(y)=3+m^2+K(u,v,w)$ and
--   $$\Xi_A(y)=\left(A-1,\frac{Am}{\sqrt3},\frac{Au}{\sqrt3},
--   \frac{Av}{\sqrt3},\frac{Aw}{\sqrt3}\right),\qquad
--   \Xi(y)=\Xi_{6/D(y)}(y).$$
--   Write $N(x)=(P,Q,r_1a,r_2b,r_3c)$ for the normalized vector field
--   and $\mathcal C(x)=C(p,s,a,b,c)$ for its constraint.
--
--   The normalized and projective state spaces are $\mathbb R^5$ and $\mathbb R^4$
--   with their finite-product norms. The maps $\Pi,\Xi,D,F$ act on these state spaces.
--
--   Define the core radius, angle, and clock factor by
--   $$r(m,v)=\sqrt{(m-1)^2+v^2},\qquad
--   \theta(m,v)=\operatorname{arsinh}\frac{1-m}{v},\qquad
--   d(r,u,w)=1-\frac{(u-w)^2}{r^2}.$$
--   For $y=(m,u,v,w)$, write $r_y=r(m,v)$, $\theta_y=\theta(m,v)$,
--   and $d_y=d(r_y,u,w)$. All quotients use the total convention $x/0=0$.
--
--   The core state space is $\mathbb R^3$ with coordinates $Y=(r,u,p)$.
--   Define
--   $$\eta(m,u,v,w)=(r(m,v),u,vw),\qquad
--   \iota_z(r,u,p)=\left(1-r\tanh z,u,\frac r{\cosh z},
--   \frac p{r/\cosh z}\right).$$
--   For fixed $(z,Y)$ put $v=r/\cosh z$, $w=p/v$, $d=d(r,u,w)$, and define
--   $$\mathcal V(z,Y)=\left(
--   \frac{-\kappa(u,v,w)-\tanh z\,(u-w)^2/r}{d},\quad
--   \frac{u[-r/2+\tanh z+w/\cosh z+(u^2-w^2)/(2r)]}{d},\quad
--   \frac{-2p(1+\kappa(u,v,w))}{rd}\right).$$
--
--   For real $k$, put $\varepsilon_k=1/(10000k)$ and define
--   $$\mathcal K_k=\{(m,u,v,w): |E(m,v)-k^2|\leq1/8,\quad v\geq1,
--   \quad0\leq u\leq\varepsilon_k,\quad0\leq vw\leq\varepsilon_k\}.$$
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   Write $G(y)=6F(y)/D(y)$, $\lambda(y)=6r_yd_y/D(y)$, and
--   $S_k(R,U,P)=(R,kU,P)$. Define
--   $$\mathcal P_y\xi=d\eta_y\xi-d\theta_y\xi\,\mathcal V(\theta_y,\eta(y)),
--   \qquad \mathcal W_{y,t_0,w}(t)=
--   \mathcal P_{\Psi_{t_0}(y,t)}(\mathcal J_{y,t_0}(t)w).$$
--   The entrance parametrization and radial exit factor are
--   $$e(k,u,w)=(1+\sqrt{k^2-1},u,1,w),$$
--   $$f_y=\mathcal V(\theta_y,\eta(y))_0,\qquad c_y=-\tanh\theta_y,
--   \qquad h_y=c_y+f_y/r_y,\qquad \rho_y=c_y/h_y.$$
--   For projective initial data $y$, put
--   $$A_{y,t_0}(t)=1+(\alpha_{\Xi(y),t_0}(t))_0.$$
--   Coordinates of three-vectors are indexed by $0,1,2$; projective
--   coordinates are indexed by $m,u,v,w$.
--
--   For $Y\in\mathbb R^3$, put $x_Y=\Xi(e(Y))$,
--   $\beta_Y(t)=\Psi_0(e(Y),t)$, and
--   $$H_Y=\{t>0:t\in I_{\max}(x_Y,0),\ (\beta_Y(t))_v=1\},
--   \qquad T(Y)=\inf H_Y,\qquad F(Y)=\eta(\beta_Y(T(Y))).$$
--   The infimum uses the total real-order convention. Write $\operatorname{Valid}(Y)$
--   when $T(Y)$ is the least element of $H_Y$, every $t\in[0,T(Y)]$ lies in
--   $I_{\max}(x_Y,0)$ with $A_{e(Y),0}(t)>0$, the active wall is strictly
--   above one for $0<t<T(Y)$, and
--   $$dg_{\alpha_{x_Y,0}(T(Y))}N(\alpha_{x_Y,0}(T(Y)))<0,
--   \qquad g(x)=(\Pi(x))_v.$$
--   All vector and operator norms below use the finite-product supremum norm.
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   For $x=(p,s,a,b,c)$, put
--   $$\psi(p,z)=\frac{\sqrt3\,z}{1+p},\qquad
--   \Pi(x)=(\psi(p,s),\psi(p,a),\psi(p,b),\psi(p,c)).$$
--   For $y=(m,u,v,w)$, set $D(y)=3+m^2+K(u,v,w)$ and
--   $$\Xi_A(y)=\left(A-1,\frac{Am}{\sqrt3},\frac{Au}{\sqrt3},
--   \frac{Av}{\sqrt3},\frac{Aw}{\sqrt3}\right),\qquad
--   \Xi(y)=\Xi_{6/D(y)}(y).$$
--   Write $N(x)=(P,Q,r_1a,r_2b,r_3c)$ for the normalized vector field
--   and $\mathcal C(x)=C(p,s,a,b,c)$ for its constraint.
--
--   The normalized and projective state spaces are $\mathbb R^5$ and $\mathbb R^4$
--   with their finite-product norms. The maps $\Pi,\Xi,D,F$ act on these state spaces.
--
--   The projective vector field in normalized time is
--   $$G(y)=\frac6{D(y)}F(y).$$
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   Put $c=u(v+w-u)$, $s(m,u,v,w)=m-1-c$,
--   $b(m,u,v,w)=(1-m^2-(v-w)^2+u^2)/2$,
--   $D(m,u,v,w)=3+m^2+K(u,v,w)$, and $r(m,v)=\sqrt{(m-1)^2+v^2}$.
--
--   Define
--   $$\mathcal C_\mu=\{(m,u,v,w):|-m-\mu|\leq1/2,
--   \ 0\leq u\leq1/10000,\ 0\leq v,w\leq1\},$$
--   $$\omega_-(y)=s(-y_m,y_u,y_v,y_w),\qquad H(y)=F(y)/\omega_-(y).$$
--   For a normalized trajectory write
--   $$\beta(t)=\Pi(\alpha_{x,t_0}(t)),\quad A(t)=1+(\alpha_{x,t_0}(t))_0,
--   \quad I=I_{\max}(x,t_0).$$
--
--   For $p=(\mu,u,w)\in\mathbb R^3$, set $e(p)=(-\mu,u,1,w)$,
--   $x_p=\Xi(e(p))$, and
--   $$T_-(p)=\inf\{t>0:t\in I_{\max}(x_p,0),\ (\Psi_0(e(p),t))_w=1\},
--   \qquad P_-(p)=\Psi_0(e(p),T_-(p)).$$
--   Let $V_-(p)$ mean that this infimum is a least element, the full interval
--   $[0,T_-(p)]$ lies in the maximal domain with positive $A$, the growing wall
--   is below one before the endpoint, and its normalized-time derivative is
--   strictly positive at the endpoint. The infimum has its total real-order meaning.
--
--   Write $e_+(R,u,w)=(1+\sqrt{R^2-1},u,1,w)$,
--   $e_-(R,u,w)=(1-\sqrt{R^2-1},u,1,w)$,
--   $p_-(R,u,w)=(\sqrt{R^2-1}-1,u,w)$, and
--   $\mathcal R(m,u,v,w)=(-m,u,w,v)$.
--   The physical connection coordinates are
--   $$\mathscr C(p)=\left(\sqrt{(-P_-(p)_0-1)^2+1},P_-(p)_1,P_-(p)_2\right).$$
--   Below $T$ denotes the canonical core return time from $e_+$ and
--   $F(Y)=\eta(\Psi_0(e_+(Y),T(Y)))$ its radial and wall coordinates.
--   Let $\mathscr R(Y)=\mathscr C(p_-(Y))$, $t_r(Y)=T_-(p_-(Y))$,
--   $G=\mathscr R\circ F$, and $t_G(Y)=T(Y)+t_r(F(Y))$.
--   A cone direction at $Y$ has $d_0=1$,
--   $|d_1|\leq\sqrt{Y_1}$, $|d_2|\leq\sqrt{Y_2}$.
--   For a map $H$ with positive output walls, its positive cone property means
--   $dH(Y)d$ has positive radial component and
--   $|(dH(Y)d)_i|\leq\sqrt{H(Y)_i}(dH(Y)d)_0$ for $i=1,2$.
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   For $x=(p,s,a,b,c)$, put
--   $$\psi(p,z)=\frac{\sqrt3\,z}{1+p},\qquad
--   \Pi(x)=(\psi(p,s),\psi(p,a),\psi(p,b),\psi(p,c)).$$
--   For $y=(m,u,v,w)$, set $D(y)=3+m^2+K(u,v,w)$ and
--   $$\Xi_A(y)=\left(A-1,\frac{Am}{\sqrt3},\frac{Au}{\sqrt3},
--   \frac{Av}{\sqrt3},\frac{Aw}{\sqrt3}\right),\qquad
--   \Xi(y)=\Xi_{6/D(y)}(y).$$
--   Write $N(x)=(P,Q,r_1a,r_2b,r_3c)$ for the normalized vector field
--   and $\mathcal C(x)=C(p,s,a,b,c)$ for its constraint.
--
--   The normalized and projective state spaces are $\mathbb R^5$ and $\mathbb R^4$
--   with their finite-product norms. The maps $\Pi,\Xi,D,F$ act on these state spaces.
--
--   The projective vector field in normalized time is
--   $$G(y)=\frac6{D(y)}F(y).$$
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   For $Y=(k,u,w)\in\mathbb R^3$, define
--   $$e_-(Y)=(1-\sqrt{k^2-1},u,1,w),\quad x_Y=\Xi(e_-(Y)),\quad
--   \beta_Y(t)=\Psi_0(e_-(Y),t),\quad g(x)=(\Pi(x))_v.$$
--   For any real height $\eta$, put
--   $$H_{\eta,Y}=\{t>0:t\in I_{\max}(x_Y,0),\ g(\alpha_{x_Y,0}(t))=\eta\},$$
--   $$T_\eta(Y)=\inf H_{\eta,Y},\qquad P_\eta(Y)=\beta_Y(T_\eta(Y)).$$
--   The infimum uses the total real-order convention. Let
--   $\operatorname{TailValid}_\eta(Y)$ mean that $T_\eta(Y)$ is the least
--   element of $H_{\eta,Y}$, and, writing $T=T_\eta(Y)$, that
--   $$t\in I_{\max}(x_Y,0),\quad 1+(\alpha_{x_Y,0}(t))_0>0
--   \quad(0\leq t\leq T),$$
--   $$g(\alpha_{x_Y,0}(t))>\eta\quad(0\leq t<T),$$
--   $$dg_{\alpha_{x_Y,0}(t)}N(\alpha_{x_Y,0}(t))<0,\quad
--   |(\Pi(\alpha_{x_Y,0}(t)))_w|<1/2\quad(0\leq t\leq T).$$
--   All vector and operator norms use the finite-product supremum norms.
--
--   For $y\in\mathbb R^4$, put $x_y=\Xi(y)$,
--   $$T_+(y)=\inf\{t>0:t\in I_{\max}(x_y,0),\ (\Psi_0(y,t))_v=1\},
--   \qquad P_+(y)=\Psi_0(y,T_+(y)).$$
--   Let $V_+(y)$ mean that this infimum is a least element, the full interval
--   $[0,T_+(y)]$ lies in the maximal domain with
--   $1+(\alpha_{x_y,0}(t))_0>0$, the active wall
--   is below one before the endpoint, and its normalized-time derivative is
--   strictly positive throughout the interval. The infimum has its total
--   real-order meaning.
--
--   For $y=(m,u,v,w)$ define the cyclic chart by
--   $$H(y)=(m+1)^2+K(u,v,w),\qquad
--   \mathcal A(y)=(1-4(m+1)/H,4v/H,4w/H,4u/H).$$
--   Its normalized symmetry is
--   $$A(p,s,a,b,c)=((-p+\sqrt3s)/2,(-\sqrt3p-s)/2,b,c,a).$$
--   Put $z_h(Y)=\mathcal A(P_h(Y))$ and
--   $$\mathcal T(h,Y)=T_h(Y)+T_+(z_h(Y)),\qquad
--   \mathcal P(h,Y)=P_+(z_h(Y)),\qquad x_Y^c=A\Xi(e_-(Y)).$$
--   Write $r(m,v)=\sqrt{(m-1)^2+v^2}$ and $g_*(x)=(\Pi(x))_v$.
--
--   In the era formulas below, $F$ denotes the core return map and
--   $G=\mathscr R\circ F$ its composition with reflection.
--   For $Z=(R,u,w)$ use the natural height $h_*(Z)=\eta((R-2)/2)^J$ and define
--   $S_*(Z)=\mathcal P(h_*(Z),Z)$,
--   $R_*(Z)=r(S_*(Z)_0,S_*(Z)_2)$,
--   $Q_*(Z)=2/R_*(Z)$ and $t_*(Z)=\mathcal T(h_*(Z),Z)$.
--   The complete era maps are
--   $$Z_m=F\circ G^m,\qquad S_m=S_*\circ Z_m,\qquad
--   R_m=R_*\circ Z_m,\qquad P_m=2/R_m.$$
--   For a graph $\Gamma=(U,W)$ write $\Gamma[r]=(r,U(r),W(r))$,
--   $\phi_m(r)=P_m(\Gamma[r])$, $k_m(r)=R_m(\Gamma[r])$,
--   $u_m(r)=S_m(\Gamma[r])_1$, $w_m(r)=S_m(\Gamma[r])_3$.
--   Let $\operatorname{Inv}_{a,b}(f)$ denote Lean's total choice inverse
--   $\operatorname{invFunOn}f\,[a,b]$. For
--   $a=2(m+1+\beta)$, $b=2(m+2-\beta)$, define
--   $$g_m=\operatorname{Inv}_{a,b}(\phi_m),\qquad h_m(y)=2/g_m(y).$$
--   Write $\gamma_n(y)=1/(n+y)$ for the Gauss inverse branch.
--   The retained phase set is
--   $\mathcal H_N=\bigcup_{m<N}(h_m(1-2\beta),h_m(2\beta))$.
--
--   A curve $\Gamma=(U,W)$ is admissible at budget $B$ if, for every $r>2$,
--   $U(r),W(r)>0$, $U(r)+W(r)\leq B$, both functions are $C^1$ at $r$,
--   and $|U'(r)|\leq\sqrt{U(r)}$, $|W'(r)|\leq\sqrt{W(r)}$.
--   For an arbitrary graph, define its successor walls by
--   $$U_m^+=\mathfrak E_{k_m,u_m}^{a,b;\,2/(1-2\beta),\,1/\beta},\qquad
--   W_m^+=\mathfrak E_{k_m,w_m}^{a,b;\,2/(1-2\beta),\,1/\beta},$$
--   where $\mathfrak E$ is the canonical amplitude extension after composing with
--   the choice inverse of $k_m$, with slope $u_m'/k_m'$ or $w_m'/k_m'$.
--   The one-step property at $(\eta,J,\sigma,B,C)$ consists of the following.
--   Put $\beta=B^\sigma$, $N=\lfloor1/\beta\rfloor_{\mathbb N}$,
--   $K_\beta=[2\beta,1-2\beta]$. One has $0<\beta<1/160$. For every $m<N$,
--   $h_m$ is strictly decreasing on $K_\beta$, and for $y\in K_\beta$,
--   $$\frac1{m+2}<h_m(y)<\frac1{m+1},\quad \phi_m(2/h_m(y))=y,
--   \quad h_m\text{ is }C^1\text{ at }y,\quad h_m'(y)<0,$$
--   $$|h_m(y)-\gamma_{m+1}(y)|\leq CB/(m+1)^2,\quad
--   \left|\log\frac{|h_m'(y)|}{|\gamma_{m+1}'(y)|}\right|\leq5C\sqrt B.$$
--   The successor $(U_m^+,W_m^+)$ is admissible at budget $B^{4/3}$ and,
--   with $r=2/h_m(y)$, satisfies
--   $k_m(r)=2/y$, $U_m^+(2/y)=u_m(r)$, $W_m^+(2/y)=w_m(r)$.
--   The retained branch intervals are pairwise disjoint and
--   $\lambda((0,1)\setminus\mathcal H_N)\leq10B^\sigma$.
--   Define
--   $$\chi(t)=\max(1-t,0),\qquad P(t)=\int_0^t\chi(u)\,du,\qquad
--   \mathcal R_{s,d,e}(x)=s+edsP(ex/s).$$
--   The integral is oriented, and division uses the total reciprocal $0^{-1}=0$.
--
--   For real functions $f,d_f$ and real endpoints $l,r$, define $F$ and $V$ by
--   $$F(x)=\begin{cases}
--   \mathcal R_{f(l),d_f(l),-1}(x-l),&x<l,\\
--   \mathcal R_{f(r),d_f(r),1}(x-r),&x\geq l,\ r<x,\\
--   f(x),&\text{otherwise},
--   \end{cases}$$
--   $$V(x)=\begin{cases}
--   d_f(l)\chi(-(x-l)/f(l)),&x<l,\\
--   d_f(r)\chi((x-r)/f(r)),&x\geq l,\ r<x,\\
--   d_f(x),&\text{otherwise}.
--   \end{cases}$$
--   Write $F_f,V_f$ when comparing several pairs of input functions.
--
--   For real functions $U,d_U$, set
--   $$r_U(x)=\sqrt{U(x)},\qquad b_U(x)=\frac{d_U(x)}{2\sqrt{U(x)}}.$$
--   Let $F_U,V_U$ be the root-curve construction applied to $(r_U,b_U)$, and set
--   $$\widetilde U(x)=F_U(x)^2.$$
--   For another pair $W,d_W$, use the analogous notation.
--
--   Let $g=\operatorname{invFunOn}k\,[a,b]$,
--   $A(t)=U(g(t))$, and $V(t)=U'(g(t))/k'(g(t))$.
--   Denote by $\mathfrak E_{k,U}^{a,b;l,r}$ the canonical amplitude extension
--   of $A,V$ from $[l,r]$, and by $\mathfrak E_{k,U}^{a,b}$ the extension
--   from $[k(b),k(a)]$.
--
--   The data includes the scalar local-inverse predicate: a $C^1$ inverse at
--   $f(a)$ taking $f(a)$ to $a$, with derivative $1/f'(a)$ and two-sided
--   inverse germs. It also includes the diagonal map $S_k(R,U,P)=(R,kU,P)$,
--   the graph restrictions, the retained phase unions, and the complete
--   one-step property of the era curve.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/tree/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_BianchiIX_Analysis_AmplitudeExtension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Real.Basic
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BianchiIX_Dynamics_CompactConnectionReturn
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_TerminalConeData
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

structure ScalarLocalInverseAt (f : ℝ → ℝ) (a : ℝ) (g : ℝ → ℝ) : Prop where
  apply_base : g (f a) = a
  contDiffAt : ContDiffAt ℝ 1 g (f a)
  hasDerivAt : HasDerivAt g (deriv f a)⁻¹ (f a)
  left_inverse : ∀ᶠ x in 𝓝 a, g (f x) = x
  right_inverse : ∀ᶠ y in 𝓝 (f a), f (g y) = y







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def graphPhase (F : (Fin 3 → ℝ) → ℝ) (U W : ℝ → ℝ) (r : ℝ) : ℝ := F ![r, U r, W r]





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def intervalRadiusInverse (k : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ := Function.invFunOn k (Icc a b)



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def retainedBranchPhases (N : ℕ) (L R : ℕ → ℝ) : Set ℝ :=
  ⋃ m ∈ Finset.range N, Ioo (R m) (L m)



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def radiusAmplitude (k U : ℝ → ℝ) (a b x : ℝ) : ℝ := U (intervalRadiusInverse k a b x)

def radiusAmplitudeSlope (k U : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  deriv U (intervalRadiusInverse k a b x) / deriv k (intervalRadiusInverse k a b x)

def radiusAmplitudeExtension (k U : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  amplitudeCurveExtension (k b) (k a) (radiusAmplitude k U a b) (radiusAmplitudeSlope k U a b)





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def radiusAmplitudeWindowExtension (k U : ℝ → ℝ) (a b l r : ℝ) : ℝ → ℝ :=
  amplitudeCurveExtension l r (radiusAmplitude k U a b) (radiusAmplitudeSlope k U a b)



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def scaleCoreVariationLinear (k : ℝ) : CoreAngleState →L[ℝ] CoreAngleState :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,
    k • ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 2]



















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Positive multipliers from an arbitrary projective initial point to its moving exit. -/
def partialCoreReturnMultiplier (τ : ProjectiveState → ℝ) (y : ProjectiveState) (i : Fin 2) : ℝ :=
  coreFlowMultiplier y 0 0 (τ y) i







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def partialCoreVariationBudget (k u p : ℝ) (v : CoreAngleState) (dz : ℝ) : ℝ :=
  |v 0| + k * |v 1| + |v 2| + (k ^ 2 * u + p / k) * |dz|













end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def partialCoreDownwardReturnTime (y : ProjectiveState) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
    projectiveOriginalFlow y 0 t 2 = 1 ∧
    normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t < 0}

def partialCoreDownwardReturnState (y : ProjectiveState) : CoreAngleState :=
  toCoreAngleState (projectiveOriginalFlow y 0 (partialCoreDownwardReturnTime y))









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def coreConnectionParameters (τ : CoreAngleState → ℝ) (Y : CoreAngleState) : ConnectionParameters :=
  coreExitConnectionParameters (coreReturnState τ Y)

def coreReflectionState (τ : CoreAngleState → ℝ) (Y : CoreAngleState) : CoreAngleState :=
  connectionReturnPhysicalState (coreConnectionParameters τ Y)





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def reflectionReturnTime (Y : CoreAngleState) : ℝ :=
  connectionReturnTime (coreExitConnectionParameters Y)

def reflectionReturnState (Y : CoreAngleState) : CoreAngleState :=
  connectionReturnPhysicalState (coreExitConnectionParameters Y)

def compactConnectionPhysicalState (η : ℝ) (Y : CoreAngleState) : CoreAngleState :=
  ![compactConnectionPhase η Y, compactConnectionState η Y 1, compactConnectionState η Y 3]











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def coreReflectionTime (Y : CoreAngleState) : ℝ :=
  reflectionReturnTime (coreReturnState coreRadiusReturnTime Y) + coreRadiusReturnTime Y



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def terminalNaturalTime (η : ℝ) (J : ℕ) (Y : ExitTailState) : ℝ :=
  terminalConnectionTime (η * ((Y 0 - 2) / 2) ^ J) Y

def terminalNaturalBoundedPhase (η : ℝ) (J : ℕ) (Y : ExitTailState) : ℝ :=
  2 / terminalNaturalPhase η J Y





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

/-- The last downward core state after `m` nonterminal reflections. -/
def eraCoreExit (m : ℕ) : CoreAngleState → CoreAngleState :=
  coreReturnState coreRadiusReturnTime ∘ (coreReflectionState coreRadiusReturnTime)^[m]

def eraBoundedPhase (η : ℝ) (J m : ℕ) : CoreAngleState → ℝ :=
  terminalNaturalBoundedPhase η J ∘ eraCoreExit m



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def eraOutputState (η : ℝ) (J m : ℕ) : CoreAngleState → ProjectiveState :=
  terminalNaturalState η J ∘ eraCoreExit m

def eraOutputRadius (η : ℝ) (J m : ℕ) : CoreAngleState → ℝ :=
  terminalNaturalPhase η J ∘ eraCoreExit m



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def eraGraphRadius (η : ℝ) (J m : ℕ) (U W : ℝ → ℝ) : ℝ → ℝ :=
  graphPhase (eraOutputRadius η J m) U W

def eraGraphWall (η : ℝ) (J m : ℕ) (U W : ℝ → ℝ) (i : Fin 4) : ℝ → ℝ :=
  graphPhase (fun X => eraOutputState η J m X i) U W



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def eraInverseBranch (η : ℝ) (J m : ℕ) (β : ℝ) (U W : ℝ → ℝ) : ℝ → ℝ :=
  fun y => 2 / intervalRadiusInverse (graphPhase (eraBoundedPhase η J m) U W)
    (2 * ((m : ℝ) + 1 + β)) (2 * ((m : ℝ) + 2 - β)) y



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def eraAmplitudeExtension (η : ℝ) (J m : ℕ) (β : ℝ) (U W : ℝ → ℝ) (i : Fin 4) : ℝ → ℝ :=
  radiusAmplitudeWindowExtension (eraGraphRadius η J m U W) (eraGraphWall η J m U W i)
    (2 * ((m : ℝ) + 1 + β)) (2 * ((m : ℝ) + 2 - β)) (2 / (1 - 2 * β)) (1 / β)



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def eraRetainedPhases (η : ℝ) (J N : ℕ) (β : ℝ) (U W : ℝ → ℝ) : Set ℝ :=
  retainedBranchPhases N (fun m => eraInverseBranch η J m β U W (2 * β))
    (fun m => eraInverseBranch η J m β U W (1 - 2 * β))



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

structure EraCurve where
  U : ℝ → ℝ
  W : ℝ → ℝ

namespace EraCurve

def state (Γ : EraCurve) (r : ℝ) : CoreAngleState := ![r, Γ.U r, Γ.W r]

def Admissible (Γ : EraCurve) (B : ℝ) : Prop :=
  ∀ r : ℝ, 2 < r → 0 < Γ.U r ∧ 0 < Γ.W r ∧ Γ.U r + Γ.W r ≤ B ∧
    ContDiffAt ℝ 1 Γ.U r ∧ ContDiffAt ℝ 1 Γ.W r ∧
    |deriv Γ.U r| ≤ Real.sqrt (Γ.U r) ∧ |deriv Γ.W r| ≤ Real.sqrt (Γ.W r)

def successor (Γ : EraCurve) (η : ℝ) (J m : ℕ) (β : ℝ) : EraCurve :=
  ⟨eraAmplitudeExtension η J m β Γ.U Γ.W 1, eraAmplitudeExtension η J m β Γ.U Γ.W 3⟩

/-- Uniform data for one actual era, its selected inverse branches, and its successor curves. -/
structure StepEstimates (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B C : ℝ) : Prop where
  beta_pos : 0 < B ^ σ
  beta_small : B ^ σ < 1 / 160
  branch : ∀ m : ℕ, m < ⌊1 / B ^ σ⌋₊ →
    let h := eraInverseBranch η J m (B ^ σ) Γ.U Γ.W
    let K := Icc (2 * B ^ σ) (1 - 2 * B ^ σ)
    StrictAntiOn h K ∧ ∀ y ∈ K,
      h y ∈ Ioo (1 / ((m : ℝ) + 2)) (1 / ((m : ℝ) + 1)) ∧
      graphPhase (eraBoundedPhase η J m) Γ.U Γ.W (2 / h y) = y ∧
      ContDiffAt ℝ 1 h y ∧ deriv h y < 0 ∧
      |h y - gaussInv ((m : ℝ) + 1) y| ≤ C * B / ((m : ℝ) + 1) ^ 2 ∧
      |Real.log (|deriv h y| / |deriv (gaussInv ((m : ℝ) + 1)) y|)| ≤ 5 * C * Real.sqrt B
  successor_admissible : ∀ m : ℕ, m < ⌊1 / B ^ σ⌋₊ →
    (Γ.successor η J m (B ^ σ)).Admissible (B ^ (4 / 3 : ℝ))
  successor_match : ∀ m : ℕ, m < ⌊1 / B ^ σ⌋₊ → ∀ y ∈ Icc (2 * B ^ σ) (1 - 2 * B ^ σ),
    let x := 2 / eraInverseBranch η J m (B ^ σ) Γ.U Γ.W y
    eraOutputRadius η J m (Γ.state x) = 2 / y ∧
      (Γ.successor η J m (B ^ σ)).U (2 / y) = eraOutputState η J m (Γ.state x) 1 ∧
      (Γ.successor η J m (B ^ σ)).W (2 / y) = eraOutputState η J m (Γ.state x) 3
  branch_disjoint : (↑(Finset.range ⌊1 / B ^ σ⌋₊) : Set ℕ).PairwiseDisjoint
    (fun m => Ioo (eraInverseBranch η J m (B ^ σ) Γ.U Γ.W (1 - 2 * B ^ σ))
      (eraInverseBranch η J m (B ^ σ) Γ.U Γ.W (2 * B ^ σ)))
  stopped_volume : volume (Ioo (0 : ℝ) 1 \ eraRetainedPhases η J ⌊1 / B ^ σ⌋₊ (B ^ σ) Γ.U Γ.W) ≤
    ENNReal.ofReal (10 * B ^ σ)



end EraCurve



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

namespace EraCurve

def constant (B : ℝ) : EraCurve := ⟨fun _ => B / 2, fun _ => B / 2⟩



/-- Unretained digits have empty branch domains; a constant curve makes their unused descendants total. -/
def nextCurve (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B : ℝ) (a : ℕ+) : EraCurve :=
  if a.natPred < ⌊1 / B ^ σ⌋₊ then Γ.successor η J a.natPred (B ^ σ)
  else constant (B ^ (4 / 3 : ℝ))

def family (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B : ℝ) (w : List ℕ+) : EraCurve :=
  w.reverseRecOn Γ (fun v a γ => γ.nextCurve η J σ (eraAmplitude B v.length) a)









end EraCurve



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def eraNextState (η : ℝ) (J m : ℕ) (X : CoreAngleState) : CoreAngleState :=
  ![eraOutputRadius η J m X, eraOutputState η J m X 1, eraOutputState η J m X 3]

def eraBudgetReturn (η : ℝ) (J m : ℕ) (p : ℝ × CoreAngleState) : ℝ × CoreAngleState :=
  (p.1 ^ (4 / 3 : ℝ), eraNextState η J m p.2)

def eraInputSelection (σ Bstar : ℝ) (m : ℕ) : Set (ℝ × CoreAngleState) :=
  {p | p.1 ∈ Ioc 0 Bstar ∧ m < ⌊1 / p.1 ^ σ⌋₊ ∧
    0 < p.2 1 ∧ 0 < p.2 2 ∧ p.2 1 + p.2 2 ≤ p.1 ∧
    p.2 0 ∈ Icc (2 * ((m : ℝ) + 1 + p.1 ^ σ)) (2 * ((m : ℝ) + 2 - p.1 ^ σ))}

def eraSelectedInputs (η : ℝ) (J : ℕ) (σ Bstar : ℝ) (m : ℕ) : Set (ℝ × CoreAngleState) :=
  {p | p ∈ eraInputSelection σ Bstar m ∧
    2 / eraOutputRadius η J m p.2 ∈ Ioo (2 * p.1 ^ σ) (1 - 2 * p.1 ^ σ)}











end BianchiIX

end
end


